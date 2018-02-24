package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._

  /*
   * CSCI 3155: Lab 3
   * Yushuo Ruan
   *
   * Partner: Yuyang Zeng
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch { case _ => Double.NaN }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case N(n) => if(n<0||n>0) true else false
      case S(s) => if(s=="") false else true
      case Undefined => false
      case _ => throw new UnsupportedOperationException
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
      // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
      case B(true) => "true"
      case B(false) => "false"
      case N(n)=> if (n.isWhole()) "%.0f" format n else n.toString
      case _ => throw new UnsupportedOperationException
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => if (s1 < s2) true else false
        case Le => if (s1 <= s2) true else false
        case Gt => if (s1 > s2) true else false
        case Ge => if (s1 >= s2) true else false
      }
      case (Undefined, Undefined) => bop match {
        case Lt => false
        case Le => false
        case Gt => false
        case Ge => false
      }
      case _ => bop match {
        case Lt => if (toNumber(v1) < toNumber(v2)) true else false
        case Le => if (toNumber(v1) <= toNumber(v2)) true else false
        case Gt => if (toNumber(v1) > toNumber(v2)) true else false
        case Ge => if (toNumber(v1) >= toNumber(v2)) true else false
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env, x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      // ****** Your cases here
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eval(env, e1)), e2)
      /* Inductive Cases */
      case Binary(bop, e1, e2) => bop match {


        case Lt | Le | Gt | Ge => B(inequalityVal(bop, eval(env, e1), eval(env, e2)))
        case Eq => (e1, e2) match {
          case (S(s1), S(s2)) => if (s1 == s2) B(true) else B(false)
          case (Undefined, Undefined) => B(true)
          case (_, _) => if (toNumber(eval(env, e1)) == toNumber(eval(env, e2))) B(true) else B(false)
        }
        case Ne => (e1, e2) match {
          case (S(s1), S(s2)) => if (s1 != s2) B(true) else B(false)
          case (Undefined, Undefined) => B(false)
          case (_, _) => if (toNumber(eval(env, e1)) != toNumber(eval(env, e2))) B(true) else B(false)
        }


        case Minus => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
        case Times => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
        case Div => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))
        case Plus => (e1, e2) match{
          case (_, S(s)) => S(toStr(eval(env, e1)) + s)
          case (S(s), _)=> S(s+toStr(eval(env,e2)))
          case (_, _) => N(toNumber(eval(env, e1)) + toNumber(eval(env, e2)))
        }


        case Or => if(toBoolean(eval(env, e1))) eval(env, e1) else eval(env, e2)
        case And => if(!toBoolean(eval(env, e1))) eval(env, e1) else eval(env, e2)


        case Seq => eval(env, e1); eval(env , e2)

      }
      case Unary(uop, e1) => uop match{
        case Neg => N(-toNumber(eval(env, e1)))
        case Not => B(!toBoolean(eval(env, e1)))
      }


      case If(e1, e2, e3) => if(toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)


      case Call(e1, e2) => eval(env, e1) match{ //Call(x+5, 7)
        case Function(None, x, e11) => { //Function(None, 'x', x+5)
          eval(extend(env, x, eval(env, e2)), e11)
        }
        case Function(Some(x1), x2, e11) => { //Function("someFuncName", 'x', x+5)
          eval(extend(extend(env, x1, eval(env, e1)), x2, eval(env, e2)), e11)
          //eval(extendX(extendF), e11)
        }
        case _ => throw new DynamicTypeError(e)
      }

      //case _ => ??? // delete this line when done
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = {
     next(e,n) match{
       case None => e
       case Some(exp) => loop(exp, n+1)
     }
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, v, x), substitute(e2, v, x))
      case If(e1, e2, e3) => If(substitute(e1, v, x),substitute(e2, v, x),substitute(e3, v, x))
      case Call(e1, e2) => Call(substitute(e1, v, x), substitute(e2, v, x))
      case Var(y) => if (x==y) v else Var(y)
      case Function(None, y, e1) => if(x == y) e else Function(None, y, substitute(e1, v, x))
      case Function(Some(y1), y2, e1) =>if(x == y1 || x == y2) e else Function(Some(y1), y2, substitute(e1, v, x))
      case ConstDecl(y, e1, e2) =>if(x == y) ConstDecl(y, substitute(e1, v, x), e2) else ConstDecl(y, substitute(e1, v, x),substitute(e2, v, x))
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      // ****** Your cases here
      case Unary(Neg, v1) if isValue(v1) => N(-toNumber(v1))
      case Unary(Not, v1) if isValue(v1) => B(!toBoolean(v1))
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
      }
      case Binary(bop @(Minus | Times | Div), v1, v2) if isValue(v1) && isValue(v2) => (bop: @unchecked) match {
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Times => N(toNumber(v1) * toNumber(v2))
        case Div => N(toNumber(v1) / toNumber(v2))
      }

      case Binary(bop @(Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      case Binary(bop @(Eq | Ne), v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (Function(_, _, _), _) => throw new DynamicTypeError(v1)
        case (_, Function(_, _, _)) => throw new DynamicTypeError(v1)
        case (v1, v2) => (bop: @unchecked) match {
          case Eq => B(v1 == v2)
          case Ne => B(v1 != v2)
        }
      }

      case Binary(And, v1, e2) if isValue(v1) => toBoolean(v1) match {
        case true => e2
        case false => v1
      }

      case Binary(Or, v1, e2) if isValue(v1) => toBoolean(v1) match {
        case true => v1
        case false => e2
      }


      case Unary(Neg, v1) if isValue(v1) => N(-toNumber(v1))
      case Unary(Not, v1) if isValue(v1) => B(!toBoolean(v1))

      case If(v1, e2, e3) if isValue(v1) => if(toBoolean(v1)) e2 else e3

      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)
      case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match {
        case Function(None, x, e3) => substitute(e3, v2, x)
        case Function(Some(x1), x2, e3) =>  substitute(substitute(e3, v1, x1), v2, x2)
        case _ => throw new DynamicTypeError(v1)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      // ****** Your cases here
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop @(Plus | Minus | Times | Div | Gt | Ge | Lt | Le), v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, v1, e2) if isValue(v1) => v1 match {
        case Function(_, _, _) => throw new DynamicTypeError(v1)
        case _ => Binary(bop, v1, step(e2))
      }

      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      case Call(Function(x1, x2, e1), e2) => Call(Function(x1, x2, e1), step(e2))
      case Call(e1, e2) => Call(step(e1), e2)


      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}