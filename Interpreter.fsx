
[<RequireQualifiedAccess>]
module Cursor =
    type Cursor = private { StringPos: int; SourceString: string }

    let advance (numChars: int) (curs: Cursor) =
        { curs with StringPos = curs.StringPos + numChars }

    let charAt (i: int) (curs: Cursor) =
        let index = curs.StringPos + i
        if index >= curs.SourceString.Length then None else Some curs.SourceString.[index]

    let eatCount (n: int) (curs: Cursor) =
        curs.SourceString.Substring(curs.StringPos, n), { curs with StringPos = curs.StringPos + n}

    let create s = { StringPos = 0; SourceString = s }

    let rec private countWhileImpl f startIndex offset (s: string): int =
        if startIndex + offset >= s.Length || f s.[startIndex + offset] |> not
        then offset
        else countWhileImpl f startIndex (offset + 1) s
    let private countWhile f (curs: Cursor) =
        countWhileImpl f curs.StringPos 0 curs.SourceString
    let eatWhile f (curs: Cursor) =
        let count = countWhile f curs
        eatCount count curs

    let skipWhile f (curs: Cursor) =
        let count = countWhile f curs
        advance count curs


type OperatorToken = | Plus | Minus | Multiply | Divide | Modulus | Equal
 
type Token =
    | Number of double
    | FnKeyword
    | FnOperator
    | Identifier of string
    | Operator of OperatorToken
    | LeftParen
    | RightParen

let inline charBetween (c: char) (a: char) (b: char) = c >= a && c <= b

let rec tokenize (curs: Cursor.Cursor) =
    let curs = Cursor.skipWhile (fun c -> c = ' ' || c = '\t' || c = '\r') curs
    seq {
        let firstChar = Cursor.charAt 0 curs
        match firstChar with
        | None -> yield! []
        | Some ch ->
            let tok, curs =
                match ch with
                | c when System.Char.IsDigit c ->
                    let s, curs = Cursor.eatWhile System.Char.IsDigit curs
                    let hasDot =
                        match Cursor.charAt 0 curs with
                        | Some '.' -> true
                        | _ -> false
                    let s, curs =
                        if hasDot then
                            let curs = Cursor.advance 1 curs
                            let restOfNum, curs = Cursor.eatWhile System.Char.IsDigit curs
                            s + "." + restOfNum, curs
                        else
                            s, curs
                    Number <| System.Double.Parse s, curs
                | c when charBetween c 'a' 'z' || charBetween c 'A' 'Z' || c = '_' ->
                    let isIdentChar chr =
                        charBetween chr 'a' 'z'
                        || charBetween chr 'A' 'Z'
                        || charBetween chr '0' '9'
                        || chr = '_'
                    let ident, curs = Cursor.eatWhile isIdentChar curs
                    let t =
                        if ident = "fn"
                        then FnKeyword
                        else Identifier ident
                    t, curs
                | '+' -> Operator Plus, Cursor.advance 1 curs
                | '-' -> Operator Minus, Cursor.advance 1 curs
                | '*' -> Operator Multiply, Cursor.advance 1 curs
                | '/' -> Operator Divide, Cursor.advance 1 curs
                | '%' -> Operator Modulus, Cursor.advance 1 curs
                | '(' -> LeftParen, Cursor.advance 1 curs
                | ')' -> RightParen, Cursor.advance 1 curs
                | '=' ->
                    let t, operatorLength =
                        match Cursor.charAt 1 curs with
                        | Some '>' -> FnOperator, 2
                        | _ -> Operator Equal, 1
                    t, Cursor.advance operatorLength curs
                | c -> failwithf "Unexpected character '%c'" c
            yield tok
            yield! tokenize curs
    }


type Ident = Ident of string

type Expression =
    | NumE of float
    | BinaryE of Op: OperatorToken * Left: Expression * Right: Expression
    | IdentifierE of Ident
    | ApplicationE of FuncName: Ident * Args: Expression list

type Associativity = | Left | Right

type OpInfo = { Precedence: int; Associativity: Associativity }

let opInfoMap =
    Map.ofList [
        (Equal, { Precedence = 1; Associativity = Right })
        (Plus, { Precedence = 2; Associativity = Left })
        (Minus, { Precedence = 2; Associativity = Left })
        (Multiply, { Precedence = 3; Associativity = Left })
        (Divide, { Precedence = 3; Associativity = Left })
        (Modulus, { Precedence = 3; Associativity = Left })
    ]

// Use "Precedence climbing" altorithm  https://eli.thegreenplace.net/2012/08/02/parsing-expressions-by-precedence-climbing
let rec parseExpr (minPrecision: int) (tokens: Token list): Expression * Token list =
    let atomLeft, tokens = parseAtom tokens
    parseExprRest minPrecision atomLeft tokens

and parseExprRest (minPrecision: int) (atomLeft: Expression) (tokens: Token list): Expression * Token list =
    let tokensSnapshot = tokens
    match atomLeft, tokens with
    | _, (Operator op)::tokens ->
        let { Precedence = prec; Associativity = assoc} = opInfoMap.[op]
        if prec < minPrecision then
            // Don't consume the operator token. If the precedence check here determines
            // that the operator precedence isn't high enough then the operator will get added
            // onto the preceding expression.
            atomLeft, tokensSnapshot
        else
            let nextMinPrecision = prec + (if assoc = Left then 1 else 0)
            let atomRight, tokens = parseExpr nextMinPrecision tokens
            let atomLeft = BinaryE(Op = op, Left = atomLeft, Right = atomRight)
            parseExprRest minPrecision atomLeft tokens
    | _, (RightParen)::_ -> atomLeft, tokensSnapshot // Don't consume the ')'
    | _, [] -> atomLeft, tokens
    // When the left hand side is an identifier, look at the next token to see
    // if it's part of a function application
    | IdentifierE ident, tokens ->
        let rec parseRight atoms tokens =
            match tokens with
            | LeftParen::_
            | (Identifier _)::_
            | (Number _)::_ ->
                let atomRight, tokens = parseAtom tokens
                parseRight (atomRight::atoms) tokens
            | _ -> atoms, tokens
        let atomsRight, tokens = parseRight [] tokens
        let atomLeft = ApplicationE(FuncName = ident, Args = List.rev atomsRight)
        parseExprRest minPrecision atomLeft tokens
    | _, x -> failwithf "Unexpected token %A" x

and parseAtom (tokens: Token list): Expression * Token list =
    match tokens with
    | LeftParen::tokens ->
        let expr, tokens = parseExpr 1 tokens
        match tokens with
        | RightParen::tokens -> expr, tokens
        | _ -> failwith "Unmatched ("
    | (Number x)::tokens -> NumE x, tokens
    | (Identifier identName)::tokens -> IdentifierE (Ident identName), tokens
    | [] -> failwith "Tokens list cannot be empty"
    | x::_ -> failwith "Unexpected token '%A'" x

type FuncDefn = { Name: Ident; Params: Ident list; Body: Expression }

type Statement =
    | Function of FuncDefn
    | ExpressionStatement of Expression

let parseStatement (tokens: Token list): Statement =
    match tokens with
    | FnKeyword::tokens ->
        let takeChoose = Seq.takeWhile Option.isSome >> Seq.choose id
        let idents =
            tokens
            |> Seq.map (function | (Identifier s) -> Some (Ident s) | _ -> None)
            |> takeChoose
            |> Seq.toList
        // Check for duplicate parameter names
        idents
        |> List.countBy (fun (Ident identName) -> identName)
        |> List.choose (fun (name, count) -> if count > 1 then Some name else None)
        |> List.iter (failwithf "Duplicate parameter names: %A")

        let tokens = tokens |> List.skip (List.length idents)
        match idents with
        | funcName::args ->
            match tokens with
            | FnOperator::tokens ->
                let expr, _ = parseExpr 1 tokens
                Function { Name = funcName; Params = args; Body = expr }
            | _ -> failwith "Expected '=>'"
        | _ -> failwith "Expected 'fn' keyword to be followed by identifiers"
    | _ -> let expr, _ = parseExpr 1 tokens in ExpressionStatement expr

let parseString (curs: Cursor.Cursor) =
    let tokens = curs |> tokenize |> Seq.toList
    match tokens with
    | [] -> None
    | _ -> Some (parseStatement tokens)

type VariableValue = | FuncRef of FuncDefn | Value of float

type Env = { Values: Map<Ident, VariableValue>; ParentEnv: Env option }
let rec findValueInEnv env ident =
    match Map.tryFind ident env.Values, env.ParentEnv with
    | Some v, _ -> Some v
    | None, Some parentEnv -> findValueInEnv parentEnv ident
    | None, None -> None

let rec evalExpr (env: Env) (expr: Expression): float * Env =

    let evalFunc (env: Env) (funcDef: FuncDefn) (argValues: float list) =
        let childMap =
            let argVals = argValues |> List.map Value
            List.zip funcDef.Params argVals |> Map.ofList
        let childEnv = { Values = childMap; ParentEnv = Some env }
        evalExpr childEnv funcDef.Body |> fst

    match expr with
    | BinaryE(Equal, left, right) ->
        match left with
        | IdentifierE ident ->
            let r, env = evalExpr env right
            match findValueInEnv env ident with
            | Some(FuncRef _) -> failwith "Attempt to assign to a variable already defined as a function"
            | _ -> ()
            let env = { env with Values = env.Values |> Map.add ident (Value r) }
            r, env
        | _ -> failwith "Expected left side of assignment to be an identifier"
    | BinaryE(op, left, right) ->
        let l, env = evalExpr env left
        let r, env = evalExpr env right
        match op with
        | Plus -> l + r, env
        | Minus -> l - r, env
        | Multiply -> l * r, env
        | Divide -> l / r, env
        | Modulus -> l % r, env
        | Equal -> failwith "Equal operator should have been handled elsewhere"
        // | Exponent -> System.Math.Pow(l, r)
    | NumE x -> x, env
    | IdentifierE (Ident identName as ident) ->
        let value = findValueInEnv env ident
        match value with
        | Some(Value x) -> x, env
        | Some(FuncRef funcDef) ->
            if not <| List.isEmpty funcDef.Params then
                failwithf "Function '%s' expects arguments but none provided" identName
            else
                // Even if it was parsed as an identifier, it might have been a function call with no arguments.
                let rslt = evalFunc env funcDef []
                rslt, env
        | None -> failwithf "Reference to undefined variable %s" identName
    | ApplicationE(funcIdentifier, args) ->
        match Map.find funcIdentifier env.Values with
        | FuncRef funcDef ->
            let (|FuncRefIdentifier|_|) (e: Expression) =
                match e with
                | (IdentifierE ident) ->
                    match findValueInEnv env ident with
                    | Some (FuncRef _) as x -> x
                    | _ -> None
                | _ -> None

            let rec evalNArgs
                    env
                    remainingCount
                    acc
                    (args:Expression list): float list * Env * Expression list =
                if remainingCount = 0 then
                    acc, env, args
                else
                    match args with
                    | (FuncRefIdentifier (FuncRef funcDef))::args ->
                        let argCountRequired = List.length funcDef.Params
                        let argVals, env, args = evalNArgs env argCountRequired [] args
                        let result = evalFunc env funcDef (List.rev argVals)
                        evalNArgs env (remainingCount - 1) (result::acc) args
                    | arg::args ->
                        let value, env = evalExpr env arg
                        evalNArgs env (remainingCount - 1) (value::acc) args
                    | [] -> acc, env, args
            let argVals, env, _ = evalNArgs env 999 [] args
            let appResult = evalFunc env funcDef (List.rev argVals)
            appResult, env
        | _ ->
            let (Ident funcName) = funcIdentifier
            failwithf "Expected '%s' to reference a function" funcName

let evalTokens env tokens =
    let stmt =
        match tokens with
        | [] -> None
        | _ -> Some (parseStatement tokens)
    match stmt with
    | Some(ExpressionStatement(expr)) ->
        let rslt, env = evalExpr env expr
        Some rslt, env
    | Some(Function(f)) ->
        match findValueInEnv env f.Name with
        | Some(Value _) ->
            let (Ident funcName) = f.Name
            failwithf "Function %s attempts to redefine existng variable" funcName
        | _ -> None, { env with Values = env.Values |> Map.add f.Name (FuncRef f) }
    | _ -> None, env

let evalString (s: string) =
    let env = { Values = Map.empty; ParentEnv = None }
    let lines = s.Split '\n'
    let folder env line =
        let tokens = tokenize (Cursor.create line)
        let _rslt, env = evalTokens env (Seq.toList tokens)
        env
    let env =
        lines
        |> Array.take ((Array.length lines) - 1)
        |> Array.fold folder env
    match Array.last lines |> Cursor.create |> parseString with
    | Some(ExpressionStatement(expr)) -> evalExpr env expr |> fst
    | _ -> failwith "Last line of string must be an expression"

let testExpr s expectedVal =
    printfn "Running testExpr: %s" s
    let result = evalString s
    if result <> expectedVal then failwithf "Expected '%s' to equal '%f', but got '%f'" s expectedVal result

testExpr "1 + 2" 3.
testExpr "1 + 2 * 3" 7.
testExpr "1 * (2 + 3)" 5.
testExpr "(1 + 2) * 3" 9.
testExpr "1 + ((1))" 2.
testExpr "((1))" 1.
testExpr "1 + 2 + 4" 7.
testExpr "9 % 2" 1.
testExpr "a = b = 6" 6.
testExpr "2.513" 2.513
testExpr "a = 1\na" 1.
testExpr "a = 1\nfn f x => a + x\nf 0" 1.
testExpr "fn f a => a\nf 2" 2.
testExpr "fn f a => a\nf (1 + 2 * 3) + 0" 7.
testExpr "fn f a b => a / b\nf 6 3" 2.

let chainedCalls = @"
fn div a b => a / b
fn add x y => x + y
add div 8 2 div 8 2"
testExpr chainedCalls 8.

let code = @"
fn one => 1
one"
testExpr code 1.
