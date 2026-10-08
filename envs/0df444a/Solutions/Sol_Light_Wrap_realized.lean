-- Prove2me | solution 1 for Light.Wrap.realized
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:21:09.531747+00:00
-- url     : https://prove2.me/submissions/3c124472-cf7c-4fc6-abee-b4f27564ae11

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Exec_bounded
import Theorems.Thm_Light_Exec_mem_outside
import Theorems.Thm_Light_polyBound_le

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h




























/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩







theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩







theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩
















































































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/







/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
@[inherit_doc] infix:50 " <' " => Cond.lt
@[inherit_doc] infix:50 " =' " => Cond.eq
@[inherit_doc] infixr:30 " ;; " => Stmt.seq



@[inherit_doc] infix:50 " ≤' " => Cond.le








/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h












































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

























/-! ## Loops whose body is a block -/














/-! ## Counting loops -/











































































end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]











/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT



















































































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}






























end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/







/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd {v : ℤ} (h : InRange W v) : (wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith

/-- Every word is the word of its signed value. -/
theorem wd_toInt (w : BitVec W) : wd W w.toInt = w := BitVec.ofInt_toInt

private theorem wd_add (a b : ℤ) : wd W a + wd W b = wd W (a + b) := (BitVec.ofInt_add a b).symm

private theorem wd_mul (a b : ℤ) : wd W a * wd W b = wd W (a * b) := (BitVec.ofInt_mul a b).symm

private theorem wd_sub (a b : ℤ) : wd W a - wd W b = wd W (a - b) := by
  rw [sub_eq_add_neg a b, wd, wd, wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

private theorem wd_one : (1 : BitVec W) = wd W 1 := BitVec.eq_of_toNat_eq rfl

/-- Numbers of absolute value at most B are in the range of words if 2 B < 2^W. -/
theorem inRange_of_abs_le {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith

/-- The initial memory holds the input in the cells 0, 1, 2, …, followed by zeros. -/
theorem loadWords_mem_nat (W : ℕ) (ws : List ℤ) (a : ℕ) :
    loadWords W ws (a : ℤ) = wd W (ws.getD a 0) := by
  simp [loadWords, show ¬ ((a : ℤ) < 0) by omega]

/-- The negative cells of the initial memory hold zeros. -/
theorem loadWords_mem_neg (W : ℕ) (ws : List ℤ) {a : ℤ} (ha : a < 0) :
    loadWords W ws a = wd W 0 := by
  simp [loadWords, ha]

/-! ## Configurations and single steps -/






















/-! ## Runs -/






theorem Steps.refl (c : Cfg W) : Steps P 0 c c := rfl

private theorem Steps.one {c c' : Cfg W} (h : step P c = .inl c') : Steps P 1 c c' := ⟨c', h, rfl⟩

/-- One run after the other. -/
theorem Steps.trans {n k : ℕ} {c c₁ c₂ : Cfg W} (h₁ : Steps P n c c₁) (h₂ : Steps P k c₁ c₂) :
    Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

/-- A run, with its last position written differently. -/
theorem Steps.cast_pos {n p p' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} (h : Steps P n c ⟨p, m⟩)
    (hp : p = p') : Steps P n c ⟨p', m⟩ := hp ▸ h

/-- A run, with its number of steps written differently. -/
theorem Steps.cast_count {n n' : ℕ} {c c' : Cfg W} (h : Steps P n c c') (hn : n = n') :
    Steps P n' c c' := hn ▸ h

/-- Within no steps there is no verdict. -/
theorem exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]

private theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  rw [exec, step]
  cases P.getD c.pc .reject <;> rfl

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by rw [exec_succ, h]

/-- A run that reaches a verdict. -/
theorem exec_of_steps {n : ℕ} {c c' : Cfg W} {v : Bool} (h : Steps P n c c')
    (hv : step P c' = .inr v) : exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h
    exact exec_succ_of_verdict hv 0
  | succ n ih =>
    obtain ⟨c₁, hs, hr⟩ := h
    rw [exec_succ_of_step hs]
    exact ih hr

/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => rwa [exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/



















/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    P.getD pos .reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    CodeAt P (pos + 1) l :=
  CodeAt.right (l₁ := [i]) h





/-! ## Straight-line code -/




















@[simp] theorem effects_nil (m : ℤ → BitVec W) : effects [] m = m := rfl

@[simp] theorem effects_cons (i : Instr) (l : List Instr) (m : ℤ → BitVec W) :
    effects (i :: l) m = effects l (effect i m) := rfl

theorem effects_append (l₁ l₂ : List Instr) (m : ℤ → BitVec W) :
    effects (l₁ ++ l₂) m = effects l₂ (effects l₁ m) := by
  simp [effects, List.foldl_append]

private theorem step_straight {c : Cfg W} {i : Instr} (h : P.getD c.pc .reject = i)
    (hi : Straight i) : step P c = .inl ⟨c.pc + 1, effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [Straight] at hi <;> simp only [step, h, effect, write, wd_one]

/-- One instruction that only changes the memory. -/
private theorem steps_instr {rest : List Instr} {pos : ℕ} {i : Instr}
    (hcode : CodeAt P pos (i :: rest)) (hi : Straight i) (m : ℤ → BitVec W) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, effect i m⟩ :=
  Steps.one (step_straight hcode.head hi)

/-- A list of instructions that only change the memory. -/
theorem steps_straight (l : List Instr) (pc : ℕ) (m : ℤ → BitVec W) (hcode : CodeAt P pc l)
    (hl : ∀ i ∈ l, Straight i) : Steps P l.length ⟨pc, m⟩ ⟨pc + l.length, effects l m⟩ := by
  induction l generalizing pc m with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 hl
    exact ⟨_, step_straight hcode.head hi,
      (ih (pc + 1) (effect i m) hcode.tail hl).cast_pos (by rw [List.length_cons]; omega)⟩

/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

/-- The only constant. -/
theorem effect_one (i : ℤ) : effect (.one i) m = Function.update m i (wd W 1) := rfl

/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.add i j k) m = Function.update m i (wd W (a + b)) := by
  rw [effect, hj, hk, wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.sub i j k) m = Function.update m i (wd W (a - b)) := by
  rw [effect, hj, hk, wd_sub]

/-- The product of two known numbers. -/
theorem effect_mul (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.mul i j k) m = Function.update m i (wd W (a * b)) := by
  rw [effect, hj, hk, wd_mul]

/-- Loading from the address a that the cell j holds. -/
theorem effect_load (i : ℤ) (hj : m j = wd W a) (ha : InRange W a) :
    effect (.load i j) m = Function.update m i (m a) := by
  rw [effect, hj, toInt_wd ha]

/-- Storing at the address a that the cell i holds. -/
theorem effect_store (j : ℤ) (hi : m i = wd W a) (ha : InRange W a) :
    effect (.store i j) m = Function.update m a (m j) := by
  rw [effect, hi, toInt_wd ha]

theorem steps_add {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.add i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a + b))⟩ :=
  effect_add i hj hk ▸ steps_instr hcode trivial m

theorem steps_sub {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.sub i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a - b))⟩ :=
  effect_sub i hj hk ▸ steps_instr hcode trivial m

theorem steps_load {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.load i j :: rest))
    (hj : m j = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (m a)⟩ :=
  effect_load i hj ha ▸ steps_instr hcode trivial m

theorem steps_store {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.store i j :: rest))
    (hi : m i = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ :=
  effect_store j hi ha ▸ steps_instr hcode trivial m

end known

/-! ## Branches and verdicts -/

/-- A branch on a cell that holds the number v: to l if v is negative, else to the next position. -/
theorem steps_bltz {rest : List Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : CodeAt P pos (.bltz c l :: rest)) (hc : m c = wd W v) (hv : InRange W v) :
    Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  refine Steps.one ?_
  simp only [step, hcode.head, hc, toInt_wd hv]

/-- A run that ends with a branch on the sign of v, where v is negative if and only if p fails. -/
theorem Steps.branch {n l pos pos' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} {v : ℤ} {p : Prop}
    (h : Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → Steps P n c ⟨pos', m⟩) ∧ (¬ p → Steps P n c ⟨l, m⟩) := by
  subst hpos
  by_cases hp : p
  · exact ⟨fun _ => by rwa [if_neg (hv.1 hp)] at h, fun h' => absurd hp h'⟩
  · exact ⟨fun h' => absurd h' hp, fun _ => by rwa [if_pos (not_not.1 (mt hv.2 hp))] at h⟩

theorem step_accept {c : Cfg W} (h : P.getD c.pc .reject = .accept) : step P c = .inr true := by
  simp only [step, h]

theorem step_reject {c : Cfg W} (h : P.getD c.pc .reject = .reject) : step P c = .inr false := by
  simp only [step, h]

/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}




theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside s m₂ m₃) :
    AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

theorem AgreeOutside.mono (h : AgreeOutside s m m') (hst : s ⊆ t) : AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h

/-- A change inside s, then a change inside t. -/
theorem AgreeOutside.trans_union (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside t m₂ m₃) :
    AgreeOutside (s ∪ t) m₁ m₃ :=
  (h₁.mono Set.subset_union_left).trans (h₂.mono Set.subset_union_right)

/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  (h ha).trans hv

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (fun e : x = a => hx (e ▸ ha)) _ _).trans (h hx)







theorem WritesIn.mono {i : Instr} (h : WritesIn s i) (hst : s ⊆ t) : WritesIn t i := by
  cases i <;> first | exact hst h | exact h

private theorem agreeOutside_effect {i : Instr} (h : WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effect i m) := by
  cases i <;>
    first | exact (AgreeOutside.refl s m).update h _ | exact AgreeOutside.refl s m | exact h.elim

/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List Instr} (h : ∀ i ∈ l, WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effects l m) := by
  induction l generalizing m with
  | nil => exact AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (agreeOutside_effect hi m).trans (ih hl _)

end framing

end ThreeSumApsp.WordRam

end
end

section


/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).
-/

@[expose] public section

namespace Light.Compiler

open EndStatement (Instr)

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/



































/-! ## Expressions and tests -/

















































/-! ## Statements -/














































































/-! ## Lengths -/





















































end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/







































section width

variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}




theorem Expr.vars_op_le_iff : (Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := max_le_iff

theorem Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff

theorem Cond.width_lt_le_iff : (Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Cond.width_eq_le_iff : (Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Stmt.width_set_le_iff : (Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := max_le_iff

theorem Stmt.width_store_le_iff : (Stmt.store a e).width ≤ F ↔ a.width ≤ F ∧ e.width ≤ F :=
  max_le_iff

theorem Stmt.width_seq_le_iff : (Stmt.seq s t).width ≤ F ↔ s.width ≤ F ∧ t.width ≤ F := max_le_iff

theorem Stmt.width_ite_le_iff :
    (Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by
  simp only [Stmt.width, max_le_iff]

theorem Stmt.width_while_le_iff : (Stmt.while c s).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F :=
  max_le_iff

theorem Stmt.width_call_le_iff :
    (Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by
  simp only [Stmt.width, max_le_iff, maxOf_le_iff, Nat.succ_le_iff]

end width

end Light

end

section


/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The numbers that never change -/










/-- A number within the limit on words is in the range of words. -/
theorem Fits.inRange {W : ℕ} {lim : Limits} {N Q : ℕ} (hfit : Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : InRange W v :=
  inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h














/-! ## Sets of cells -/



























/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/

theorem mem_temps_iff {k F : ℕ} {a : ℤ} :
    a ∈ Temps k F ↔ a = cADDR ∨ cT (2 * F) ≤ a ∧ a ≤ cT k ∧ 4 ∣ cT 0 - a := by
  simp only [Temps, cT, Set.mem_ofPred_eq]
  refine or_congr_right ⟨?_, fun h => ⟨((-23 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨j, hk, hj, rfl⟩
    omega
  · omega

theorem mem_stack_iff {q Q : ℕ} {a : ℤ} :
    a ∈ Stack q Q ↔ cStack Q < a ∧ a ≤ cStack q ∧ 2 ∣ a := by
  simp only [Stack, cStack, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨(-a / 2).toNat, ?_⟩⟩
  · rintro ⟨j, hq, hj, rfl⟩
    omega
  · omega

theorem mem_pool_iff {N : ℕ} {a : ℤ} :
    a ∈ Pool N ↔ cPool N ≤ a ∧ a ≤ cPool 0 ∧ 4 ∣ cPool 0 - a := by
  simp only [Pool, cPool, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨((-25 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨n, hn, rfl⟩
    omega
  · omega























variable {W : ℕ} {Z : Sizes W} {F : ℕ}

/-- What an expression may change is scratch. -/
theorem temps_subset_scratch {k : ℕ} : Temps k F ⊆ Scratch F := by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                               Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                               Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                               Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                               Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                               Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                               Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                               Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                               Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                               Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                               Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                               or_false] <;>
                                                                             intros <;>
                                                                           omega)

/-- A statement may change scratch cells. -/
theorem scratch_subset_writable {q : ℕ} : Scratch Z.F ⊆ Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left

/-- A statement may change the stack from its frame on. -/
theorem stack_subset_writable {q : ℕ} : Stack q Z.Q ⊆ Writable Z q :=
  Set.subset_union_right.trans Set.subset_union_left

/-- A statement in a later frame may change less. -/
theorem writable_subset_writable {q q' : ℕ} (h : q ≤ q') : Writable Z q' ⊆ Writable Z q :=
  Set.union_subset_union_left _ (Set.union_subset_union_right _ (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                            Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                            or_false] <;>
                                                                          intros <;>
                                                                        omega)))

/-- A statement may change the memory cells within the limits. -/
theorem mem_writable_of_addr {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ Writable Z q :=
  Set.mem_union_right _ h

/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : cStack q - ((2 * x : ℕ) : ℤ) = cStack (q + x) := by
  simp only [cStack]
  push_cast
  ring

/-- Back from the frame q + x to the frame q. -/
theorem cStack_add (q x : ℕ) : cStack (q + x) + ((2 * x : ℕ) : ℤ) = cStack q := by
  simp only [cStack]
  push_cast
  ring

/-- The stack cell before the cell q + 1. -/
theorem cStack_succ_add (q : ℕ) : cStack (q + 1) + ((2 : ℕ) : ℤ) = cStack q := cStack_add q 1

/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : InRange W (cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [cStack] <;> linarith [Z.fits.stack]

/-- The addresses of the memory fit in a word. -/
theorem Sizes.inRange_addr (Z : Sizes W) {a : ℤ} (h : Z.lim.Addr a) : InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]

/-- The number -1, on which every jump branches, fits in a word. -/
theorem Sizes.inRange_neg_one (Z : Sizes W) : InRange W (-1) := by
  have hN : (2 : ℤ) ≤ Z.disp := by
    exact_mod_cast (Nat.le_mul_of_pos_right 2 Z.F.succ_pos).trans Z.offsets_le
  constructor <;> linarith [Z.fits.pool_lt]

/-! ## The relation between a state of the light language and a memory of the machine -/











section Rel

variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : Rel Z σ q m) (A : AgreeOutside s m m')
    (hs : s ⊆ (Constants Z.disp)ᶜ) (hfp : m' cFP = wd W (cStack q'))
    (hloc : ∀ x < Z.F, m' (cStack (q' + x)) = wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = wd W (σ'.mem a)) : Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                             Light.Compiler.Scratch, Light.Compiler.Writable,
                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                             or_false] <;>
                           intros <;>
                         omega))).trans R.one
    zero := (keep (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                              Light.Compiler.Scratch, Light.Compiler.Writable,
                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                              or_false] <;>
                            intros <;>
                          omega))).trans R.zero
    neg := (keep (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                             Light.Compiler.Scratch, Light.Compiler.Writable,
                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                             or_false] <;>
                           intros <;>
                         omega))).trans R.neg
    pool := fun n hn => (keep (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                          or_false] <;>
                                        intros <;>
                                      omega))).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : Rel Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                  Light.Compiler.Scratch, Light.Compiler.Writable,
                                  Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                  Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                  Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                  Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                  Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                  Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                  Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                  or_false] <;>
                                intros <;>
                              omega)) (A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                          or_false] <;>
                                                        intros <;>
                                                      omega)) R.fp)
    (fun x hx => A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega)) (R.loc x hx)) fun a ha => A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                     or_false] <;>
                                                                                   intros <;>
                                                                                 omega)) (R.mem a ha)

/-- A memory that differs only in scratch cells and in the stack beyond the frame represents the
same state.  (Here and below 1 ≤ q is needed because stack cell 0 is memory cell 0.) -/
theorem Rel.beyond (R : Rel Z σ q m) (hq : 1 ≤ q)
    (A : AgreeOutside (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                  Light.Compiler.Scratch, Light.Compiler.Writable,
                                  Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                  Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                  Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                  Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                  Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                  Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                  Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                  or_false] <;>
                                intros <;>
                              omega)) (A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                          or_false] <;>
                                                        intros <;>
                                                      omega)) R.fp)
    (fun x hx => A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega)) (R.loc x hx)) fun a ha => A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                     or_false] <;>
                                                                                   intros <;>
                                                                                 omega)) (R.mem a ha)

/-- Writing a local variable. -/
private theorem Rel.setLoc (R : Rel Z σ q m) (hq : 1 ≤ q) (x : ℕ) (v : ℤ) :
    Rel Z { σ with loc := Function.update σ.loc x v } q
      (Function.update m (cStack (q + x)) (wd W v)) := by
  refine R.of_agreeOutside ((AgreeOutside.refl {cStack (q + x)} m).update rfl _) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                             Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                             or_false] <;>
                                                                                           intros <;>
                                                                                         omega))
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact R.fp))) (fun y hy => ?_) fun a ha => by ((repeat
                                                               (first
                                                                 | rw [Function.update_self]
                                                                 |
                                                                   rw [Function.update_of_ne
                                                                       (by
                                                                         (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                                 Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                                 Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                                 Set.mem_union, Set.mem_insert_iff,
                                                                                 Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                                                                 Light.Compiler.mem_temps_iff,
                                                                                 Light.Compiler.mem_stack_iff,
                                                                                 Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                                                                 Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                 Light.Compiler.cONE, Light.Compiler.cZERO,
                                                                                 Light.Compiler.cNEG, Light.Compiler.cFP,
                                                                                 Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                 Light.Compiler.cRR, Light.Compiler.cNFP,
                                                                                 Light.Compiler.cD, Light.Compiler.cT,
                                                                                 Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                                                                 false_or, or_false] <;>
                                                                               intros <;>
                                                                             omega))]));
                                                           (exact R.mem a ha))
  obtain rfl | hxy := eq_or_ne y x
  · simp
  · rw [Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                           Light.Compiler.Scratch, Light.Compiler.Writable,
                                           Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                           Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                           Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                           Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                           Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                           Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                           Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                           Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                           Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                           or_false] <;>
                                         intros <;>
                                       omega))]
    exact (R.loc y hy).trans (by simp [hxy])

/-- Writing a memory cell. -/
theorem Rel.setMem (R : Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (wd W v)) := by
  -- the address is not negative, so it is no register and no stack cell of the frame
  have hnonneg : 0 ≤ a := ha.1
  refine R.of_agreeOutside ((AgreeOutside.refl {a} m).update rfl _) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                or_false] <;>
                                                                              intros <;>
                                                                            omega))
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact R.fp))) (fun x hx => by ((repeat
                                               (first
                                                 | rw [Function.update_self]
                                                 |
                                                   rw [Function.update_of_ne
                                                       (by
                                                         (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                 Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                 Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                 Set.mem_union, Set.mem_insert_iff,
                                                                 Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                                                 Light.Compiler.mem_temps_iff,
                                                                 Light.Compiler.mem_stack_iff,
                                                                 Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                                                 Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                 Light.Compiler.cONE, Light.Compiler.cZERO,
                                                                 Light.Compiler.cNEG, Light.Compiler.cFP,
                                                                 Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                 Light.Compiler.cRR, Light.Compiler.cNFP,
                                                                 Light.Compiler.cD, Light.Compiler.cT,
                                                                 Light.Compiler.cPool, Light.Compiler.cStack,
                                                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                                                 false_or, or_false] <;>
                                                               intros <;>
                                                             omega))]));
                                           (exact R.loc x hx))) fun b hb => ?_
  obtain rfl | hab := eq_or_ne b a.toNat
  · simp [Int.toNat_of_nonneg hnonneg]
  · rw [Function.update_of_ne (by omega)]
    exact (R.mem b hb).trans (by simp [hab])

/-- Reading a memory cell. -/
theorem Rel.read (R : Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this

/-- The cell to which FP points is local variable 0. -/
theorem Rel.loc_zero (R : Rel Z σ q m) (hF : 0 < Z.F) : m (cStack q) = wd W (σ.loc 0) :=
  R.loc 0 hF

end Rel








/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

/-- A memory that differs only in scratch cells represents the same state in the same frame. -/
theorem Framed.same (I : Framed Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩

/-- An unconditional jump. -/
theorem steps_jump {l : ℕ} (hcode : CodeAt code pos (.bltz cNEG l :: rest))
    (hneg : m cNEG = wd W (-1)) (hr : InRange W (-1)) : Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using steps_bltz hcode hneg hr

/-- The two instructions that put the content v of the cell c into the local variable x. -/
theorem steps_setVar {x : ℕ} {c v : ℤ} (I : Framed Z σ q m) (hx : x < Z.F)
    (hcode : CodeAt code pos (.sub cADDR cFP (cPool (2 * x)) :: .store cADDR c :: rest))
    (hc : m c = wd W v) (hne : c ≠ cADDR) :
    ∃ m', Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      AgreeOutside (Writable Z q) m m' := by
  have hN := Z.offsets_le
  have hQ := I.high
  -- ADDR := FP - 2 x
  have run₁ := steps_sub (i := cADDR) hcode I.rel.fp (I.rel.pool (2 * x) (by omega))
  rw [cStack_sub] at run₁
  have A₁ := (AgreeOutside.refl (Scratch Z.F) m).update (a := cADDR) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                   Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                   Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                   Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                   Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                   Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                   Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                   Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                   Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                   Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                   Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                   or_false] <;>
                                                                                 intros <;>
                                                                               omega))
    (wd W (cStack (q + x)))
  -- the cell at ADDR := c
  have run₂ := run₁.trans (steps_store hcode.tail (Function.update_self _ _ _)
    (Z.inRange_stack (by omega)))
  rw [Function.update_of_ne hne, hc] at run₂
  exact ⟨_, run₂, (I.rel.same A₁).setLoc I.low x v,
    (A₁.mono scratch_subset_writable).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                           Light.Compiler.Scratch, Light.Compiler.Writable,
                                                           Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                           Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                           Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                           Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                           Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                           Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                           Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                           Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                           Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                           or_false] <;>
                                                         intros <;>
                                                       omega)) _⟩

end code

end Light.Compiler

end
end

section


/-!
# The compiler is correct on expressions

The code of an expression e, compiled for the temporary T_k, only changes the memory
(`straight_compileExpr`).  Run in a memory that represents the state σ, it leaves the value of e in
T_k and changes nothing but ADDR and the temporaries from T_k on.  That is `effects_compileExpr`,
for an expression that needs no more temporaries than there are from T_k on, and
`effects_compileExpr_of_width`, the form that the other files use, for an expression of width at
most F.

The proof is an induction on e; in each case the instructions are run one after the other.  A
constant is built from its binary digits (`effects_digitsCode`).  For an operation, the value of the
left side waits in T_k while the right side is evaluated into T_{k+1}, which does not touch T_k.
-/

public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {F : ℕ}

/-- Every expression uses at least one temporary. -/
private theorem _root_.Light.Expr.height_pos (e : Expr) : 0 < e.height := by
  induction e with
  | const n => simp [Expr.height]
  | var x => simp [Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih

/-- The temporary that receives the value of an expression is one of those that its code may
change. -/
private theorem cT_mem_temps_of_height (e : Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) :
    cT k ∈ Temps k F := by
  have := e.height_pos
  (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
          Light.Compiler.Scratch, Light.Compiler.Writable,
          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
          or_false] <;>
        intros <;>
      omega)

/-! ## Constants -/

private theorem straight_digitsCode (c : ℤ) : ∀ L : List ℕ, ∀ i ∈ digitsCode c L, Straight i
  | [] => by simp [digitsCode, Straight]
  | d :: L => by
    have := straight_digitsCode c L
    by_cases hd : d = 0 <;> simpa [digitsCode, hd, Straight, or_imp, forall_and] using this

/-- The code for a constant: the cell c receives the number with the given binary digits, and
nothing else changes. -/
private theorem effects_digitsCode {c : ℤ} (hc : cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2)
    (m : ℤ → BitVec W) (hone : m cONE = wd W 1) :
    effects (digitsCode c L) m c = wd W (Nat.ofDigits 2 L : ℕ) ∧
      AgreeOutside {c} m (effects (digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    rw [digitsCode, effects_cons, effects_nil,
      effect_sub c (wd_toInt (m c)).symm (wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L ih =>
    obtain ⟨val, A⟩ := ih fun x hx => hL x (by simp [hx])
    -- c := c + c
    rw [digitsCode, effects_append, effects_append, effects_cons, effects_nil, effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      rw [if_neg one_ne_zero, effects_cons, effects_nil, effect_add c (Function.update_self _ _ _)
        ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring

/-! ## Expressions -/

private theorem straight_instr (o : Op) (i j k : ℤ) : Straight (o.instr i j k) := by
  cases o <;> trivial

/-- The code of an expression only changes the memory. -/
theorem straight_compileExpr : ∀ (e : Expr) (k : ℕ), ∀ i ∈ compileExpr e k, Straight i
  | .const _, _ => straight_digitsCode _ _
  | .var _, _ => by simp [compileExpr, Straight]
  | .op o a b, k => List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨straight_compileExpr a k, straight_compileExpr b (k + 1)⟩, by simp [straight_instr]⟩
  | .load a, k => List.forall_mem_append.2 ⟨straight_compileExpr a k, by simp [Straight]⟩

/-- The instruction of an operation, on cells that hold known numbers. -/
private theorem effect_instr (o : Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = wd W a)
    (hk : m k = wd W b) : effect (o.instr i j k) m = Function.update m i (wd W (o.eval a b)) := by
  cases o
  exacts [effect_add i hj hk, effect_sub i hj hk, effect_mul i hj hk]

variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-- The code of an expression leaves its value in T_k and changes nothing but ADDR and the
temporaries from T_k on. -/
private theorem effects_compileExpr (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hvars : e.vars ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hT : k + e.height ≤ 2 * Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) := by
  induction e generalizing k m with
  | const n =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ := effects_digitsCode (c := cT k) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                      Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                      Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                      Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                      Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                      Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                      Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                      Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                      Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                      Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                      Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                      or_false] <;>
                                                                    intros <;>
                                                                  omega)) (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    -- ADDR := FP - 2 x; T_k := the cell at ADDR
    rw [compileExpr, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)), cStack_sub,
      effect_load (cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨?_, ((AgreeOutside.refl _ m).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                              Light.Compiler.Scratch, Light.Compiler.Writable,
                                                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                              or_false] <;>
                                                            intros <;>
                                                          omega)) _).update hk _⟩
    rw [Function.update_self, Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                or_false] <;>
                                                              intros <;>
                                                            omega)), I.rel.loc x hx, Expr.val]
  | op o a b iha ihb =>
    have hk := cT_mem_temps_of_height _ hT
    have hha : a.height ≤ (Expr.op o a b).height := le_max_left _ _
    have hhb : b.height + 1 ≤ (Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ := ihb (I.same (Aa.mono temps_subset_scratch)) (k + 1) hwb hsb (by omega)
    -- T_k := T_k o T_{k+1}
    rw [compileExpr, effects_append, effects_append, effects_cons, effects_nil,
      effect_instr o (cT k) (Ab.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                 Light.Compiler.Scratch, Light.Compiler.Writable,
                                                 Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                 Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                 Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                 Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                 Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                 Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                 Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                 Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                 or_false] <;>
                                               intros <;>
                                             omega)) va) vb]
    exact ⟨Function.update_self _ _ _,
      (Aa.trans (Ab.mono (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                     or_false] <;>
                                   intros <;>
                                 omega)))).update hk _⟩
  | load a ih =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    -- the address is not negative, so it is neither ADDR nor a temporary
    have hnonneg : 0 ≤ a.val σ := haddr.1
    -- T_k := the cell at T_k
    rw [compileExpr, effects_append, effects_cons, effects_nil,
      effect_load (cT k) va (Z.inRange_addr haddr), Aa.cell (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                        Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                        Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                        Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                        Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                        Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                        Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                        Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                        Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                        Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                        Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                        or_false] <;>
                                                                      intros <;>
                                                                    omega)), I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩

/-- The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
its value in T_k and changes nothing but ADDR and the temporaries from T_k on. -/
theorem effects_compileExpr_of_width (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) :=
  effects_compileExpr I e k (Expr.width_le_iff.1 hw).1 hs
    (by have := (Expr.width_le_iff.1 hw).2; omega)

end Light.Compiler

end
end

section


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/














/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.
-/

public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}








/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | .const n, h => by
    rw [Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | .var x, _ => hσ.1 x
  | .op _ _ _, h => h.2.2
  | .load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ :=
  ⟨ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : State} (hσ : σ.Bounded lim) (args : List Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : State.Bounded lim ⟨frame (args.map (·.val σ)), σ.mem⟩ := by
  refine bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact Expr.abs_val_le hσ e (ha e he)

































end Light

end
end

section


/-!
# The compiler is correct on tests

The code of a test goes on to the next position if the test holds and jumps to a given position if
it does not, in at most as many steps as it has instructions, and it changes scratch cells only.
This behaviour is called `Decides`, and `decides_compileCond` proves it.

Both tests first evaluate a into T₀ and b into T₁ (`steps_pair`, which also serves the statement
that stores into the memory).  For a < b the code forms D = b - a - 1 and leaves if D < 0
(`decides_lt`).  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative (`decides_eq`).  No difference overflows, because words hold twice the largest value and
one more (`inRange_sub`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}

/-! ## Two expressions -/

/-- What follows the code of two expressions. -/
theorem codeAt_after_pair (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) :
    CodeAt code (pos + (a.size + b.size)) rest :=
  hcode.right.cast_pos (by rw [List.length_append, length_compileExpr, length_compileExpr])

/-- The code of two expressions, one after the other, leaves their values in T₀ and T₁ and changes
scratch cells only. -/
theorem steps_pair (I : Framed Z σ q m)
    (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) (hwa : a.width ≤ Z.F)
    (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m', Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
      m' (cT 0) = wd W (a.val σ) ∧ m' (cT 1) = wd W (b.val σ) ∧
      AgreeOutside (Scratch Z.F) m m' := by
  obtain ⟨va, Aa⟩ := effects_compileExpr_of_width I a 0 hwa hsa (by omega)
  have Aa' := Aa.mono temps_subset_scratch
  obtain ⟨vb, Ab⟩ := effects_compileExpr_of_width (I.same Aa') b 1 hwb hsb (by omega)
  have run := steps_straight _ pos m hcode.left
    (List.forall_mem_append.2 ⟨straight_compileExpr a 0, straight_compileExpr b 1⟩)
  rw [List.length_append, length_compileExpr, length_compileExpr, effects_append] at run
  exact ⟨_, run, Ab.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                       or_false] <;>
                                     intros <;>
                                   omega)) va, vb, Aa'.trans (Ab.mono temps_subset_scratch)⟩

/-! ## Tests -/








/-- The test holds. -/
theorem Decides.of_holds {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ :=
  let ⟨m', n, le, A, run, _⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- The test fails. -/
theorem Decides.of_fails {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : ¬ p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨l, m'⟩ :=
  let ⟨m', n, le, A, _, run⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- No overflow: the difference of two values fits in a word, and so does one less. -/
private theorem inRange_sub (Z : Sizes W) {x y : ℤ} (hx : |x| ≤ Z.lim.word)
    (hy : |y| ≤ Z.lim.word) : InRange W (x - y) ∧ InRange W (x - y - 1) := by
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := And.intro (abs_le.1 hx) (abs_le.1 hy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Z.fits.word]

/-- The test a < b. -/
private theorem decides_lt (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.lt a b) l)) (hw : (Cond.lt a b).width ≤ Z.F)
    (hs : (Cond.lt a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.lt a b).size l m (a.val σ < b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_lt_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := b - a
  have run₂ := run₁.trans (steps_sub restCode vb va)
  -- D := D - 1
  have run₃ := run₂.trans (steps_sub restCode.tail (Function.update_self _ _ _)
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact (I.rel.same A₁).one))))
  -- leave if D < 0
  have run₄ := run₃.trans (steps_bltz restCode.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z (Expr.abs_val_le hσ b hsb) (Expr.abs_val_le hσ a hsa)).2)
  exact ⟨_, _, by rw [Cond.size], (A₁.update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                             Light.Compiler.Scratch, Light.Compiler.Writable,
                                                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                             or_false] <;>
                                                           intros <;>
                                                         omega)) _).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                       or_false] <;>
                                                                                     intros <;>
                                                                                   omega)) _,
    run₄.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The test a = b. -/
private theorem decides_eq (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.eq a b) l)) (hw : (Cond.eq a b).width ≤ Z.F)
    (hs : (Cond.eq a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.eq a b).size l m (a.val σ = b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_eq_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  have ha := Expr.abs_val_le hσ a hsa
  have hb := Expr.abs_val_le hσ b hsb
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := a - b
  have run₂ := run₁.trans (steps_sub restCode va vb)
  have A₂ := A₁.update (a := cD) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                 Light.Compiler.Scratch, Light.Compiler.Writable,
                                                 Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                 Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                 Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                 Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                 Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                 Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                 Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                 Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                 or_false] <;>
                                               intros <;>
                                             omega)) (wd W (a.val σ - b.val σ))
  -- leave if D < 0
  have run₃ := run₂.trans (steps_bltz restCode.tail (Function.update_self _ _ _)
    (inRange_sub Z ha hb).1)
  by_cases hlt : a.val σ - b.val σ < 0
  · rw [if_pos hlt] at run₃
    exact ⟨_, _, by rw [Cond.size]; omega, A₂, fun h => absurd h (by omega), fun _ => run₃⟩
  rw [if_neg hlt] at run₃
  -- D := 0 - D
  have run₄ := run₃.trans (steps_sub restCode.tail.tail
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact (I.rel.same A₁).zero)))
    (Function.update_self _ _ _))
  rw [zero_sub, neg_sub] at run₄
  -- leave if D < 0
  have run₅ := run₄.trans (steps_bltz restCode.tail.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z hb ha).1)
  exact ⟨_, _, by rw [Cond.size], A₂.update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                            Light.Compiler.Scratch, Light.Compiler.Writable,
                                                            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                            or_false] <;>
                                                          intros <;>
                                                        omega)) _,
    run₅.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The code of a test decides the test. -/
theorem decides_compileCond (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : Cond)
    (hcode : CodeAt code pos (compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    Decides code Z.F pos c.size l m (c.Holds σ) := by
  cases c with
  | lt a b => exact decides_lt I hσ hcode hw hs
  | eq a b => exact decides_eq I hσ hcode hw hs

end Light.Compiler

end
end

section


/-!
# Pieces of a call: the arguments and the new frame

A call first evaluates its arguments into T₀, T₁, … (`effects_argsCode`).  Then it sets up the frame
of the procedure, F + 1 stack cells further on (`effects_newFrame`): NFP receives the new frame
pointer, the local variables of the new frame receive the arguments and zeros
(`effects_frameInit`), the stack cell before the new frame receives the position to return to, and
FP moves to the new frame.  After that the memory represents the state in which the procedure
starts.
-/

public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-! ## The arguments -/

/-- The code of the arguments only changes the memory. -/
theorem straight_argsCode : ∀ (es : List Expr) (k : ℕ), ∀ i ∈ argsCode es k, Straight i
  | [], _ => by simp [argsCode]
  | e :: es, k => List.forall_mem_append.2 ⟨straight_compileExpr e k, straight_argsCode es (k + 1)⟩

/-- The code of the arguments leaves their values in T_k, T_{k+1}, … and changes nothing but ADDR
and the temporaries from T_k on. -/
theorem effects_argsCode (I : Framed Z σ q m) (es : List Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        effects (argsCode es k) m (cT (k + i)) = wd W (frame (es.map (·.val σ)) i)) ∧
      AgreeOutside (Temps k Z.F) m (effects (argsCode es k) m) := by
  induction es generalizing k m with
  | nil => exact ⟨fun i h => absurd h (by simp), AgreeOutside.refl _ m⟩
  | cons e es ih =>
    obtain ⟨hwe, hwes⟩ := List.forall_mem_cons.1 hw
    obtain ⟨hse, hses⟩ := List.forall_mem_cons.1 hs
    rw [List.length_cons] at hk
    obtain ⟨ve, Ae⟩ := effects_compileExpr_of_width I e k hwe hse (by omega)
    obtain ⟨ves, Aes⟩ := ih (I.same (Ae.mono temps_subset_scratch)) (k + 1) hwes hses (by omega)
    rw [argsCode, effects_append]
    refine ⟨fun i hi => ?_, Ae.trans (Aes.mono (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                             Light.Compiler.Scratch, Light.Compiler.Writable,
                                                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                             or_false] <;>
                                                           intros <;>
                                                         omega)))⟩
    cases i with
    | zero => exact Aes.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                         Light.Compiler.Scratch, Light.Compiler.Writable,
                                         Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                         Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                         Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                         Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                         Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                         Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                         Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                         Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                         Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                         or_false] <;>
                                       intros <;>
                                     omega)) ve
    | succ i =>
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact ves i (by simpa using hi)

/-! ## The new frame -/

/-- The code for one more local variable. -/
private theorem frameInit_succ (F' n : ℕ) : frameInit (F' + 1) n = frameInit F' n ++
    [.sub cADDR cNFP (cPool (2 * F')), .store cADDR (if F' < n then cT F' else cZERO)] := by
  simp [frameInit, List.range_succ, List.flatMap_append]

private theorem straight_frameInit (n : ℕ) : ∀ F' : ℕ, ∀ i ∈ frameInit F' n, Straight i
  | 0 => by simp [frameInit]
  | F' + 1 => by
    rw [frameInit_succ]
    exact List.forall_mem_append.2 ⟨straight_frameInit n F', by simp [Straight]⟩

/-- The code that fills the first F' local variables of the new frame at q': the first n from the
temporaries, the others with 0.  It changes nothing but ADDR and stack cells from q' on. -/
private theorem effects_frameInit (Z : Sizes W) (n q' F' : ℕ) (m : ℤ → BitVec W)
    (hNFP : m cNFP = wd W (cStack q'))
    (hpool : ∀ i < F', m (cPool (2 * i)) = wd W ((2 * i : ℕ) : ℤ)) (hQ : q' + F' ≤ Z.Q) :
    (∀ i < F',
        effects (frameInit F' n) m (cStack (q' + i)) = if i < n then m (cT i) else m cZERO) ∧
      AgreeOutside (insert cADDR (Stack q' Z.Q)) m (effects (frameInit F' n) m) := by
  induction F' with
  | zero => exact ⟨fun i h => absurd h (by omega), AgreeOutside.refl _ m⟩
  | succ F' ih =>
    obtain ⟨val, A⟩ := ih (fun i hi => hpool i (by omega)) (by omega)
    -- ADDR := NFP - 2 F'; the cell at ADDR := T_{F'} or 0
    rw [frameInit_succ, effects_append, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR (A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                           Light.Compiler.Scratch, Light.Compiler.Writable,
                                           Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                           Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                           Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                           Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                           Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                           Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                           Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                           Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                           Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                           or_false] <;>
                                         intros <;>
                                       omega)) hNFP) (A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                         Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                         Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                         Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                         Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                         Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                         Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                         Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                         Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                         Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                         Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                         or_false] <;>
                                                                       intros <;>
                                                                     omega)) (hpool F' (by omega))),
      cStack_sub, effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨fun i hi => ?_, (A.update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                    or_false] <;>
                                                  intros <;>
                                                omega)) _).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                              Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                              or_false] <;>
                                                                            intros <;>
                                                                          omega)) _⟩
    obtain rfl | hne := eq_or_ne i F'
    · rw [Function.update_self]
      split_ifs <;> rw [Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                          or_false] <;>
                                                        intros <;>
                                                      omega)), A.cell (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                  Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                  Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                  Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                  Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                  Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                  Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                  Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                  Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                  or_false] <;>
                                                                                intros <;>
                                                                              omega))]
    · ((repeat
             (first
               | rw [Function.update_self]
               |
                 rw [Function.update_of_ne
                     (by
                       (simp only [Set.subset_def, Set.mem_compl_iff,
                               Light.Compiler.Constants, Light.Compiler.Scratch,
                               Light.Compiler.Writable, Light.Compiler.MainFrame,
                               Set.mem_union, Set.mem_insert_iff,
                               Set.mem_singleton_iff, Set.mem_ofPred_eq,
                               Light.Compiler.mem_temps_iff,
                               Light.Compiler.mem_stack_iff,
                               Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                               Light.Compiler.cARG2, Light.Compiler.cRESULT,
                               Light.Compiler.cONE, Light.Compiler.cZERO,
                               Light.Compiler.cNEG, Light.Compiler.cFP,
                               Light.Compiler.cADDR, Light.Compiler.cRET,
                               Light.Compiler.cRR, Light.Compiler.cNFP,
                               Light.Compiler.cD, Light.Compiler.cT,
                               Light.Compiler.cPool, Light.Compiler.cStack,
                               Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                               false_or, or_false] <;>
                             intros <;>
                           omega))]));
         (exact val i (by omega)))

/-- The code of the new frame only changes the memory. -/
theorem straight_newFrame (F n ret : ℕ) : ∀ i ∈ newFrame F n ret, Straight i :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨by simp [Straight], straight_frameInit n F⟩,
    by simp [Straight]⟩

/-- The new frame.  If T₀, T₁, … hold the values of the arguments, then afterwards the memory
represents the state in which the procedure starts, in the frame q + F + 1, and the stack cell
before that frame holds the position to return to.  Of the stack, only cells from q + F on have
changed. -/
theorem effects_newFrame (I : Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List Expr)
    (hargs : ∀ i < args.length, m (cT i) = wd W (frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    Rel Z ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (effects (newFrame Z.F args.length ret) m) ∧
      effects (newFrame Z.F args.length ret) m (cStack (q + Z.F)) = wd W ret ∧
      AgreeOutside (Writable Z (q + Z.F)) m (effects (newFrame Z.F args.length ret) m) := by
  have R := I.rel
  have hq := I.low
  have hN := Z.offsets_le
  simp only [newFrame, effects_append, effects_cons, effects_nil]
  -- NFP := FP - 2 (F + 1).  Up to the last instruction, only scratch cells and the stack beyond the
  -- frame q change, so the memory goes on representing σ in the frame q.
  rw [effect_sub cNFP R.fp (R.pool _ hN), cStack_sub, ← Nat.add_assoc]
  have A₁ := (AgreeOutside.refl (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m).update (a := cNFP) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                                          or_false] <;>
                                                                                                        intros <;>
                                                                                                      omega))
    (wd W (cStack (q + Z.F + 1)))
  -- the local variables of the new frame
  obtain ⟨val, A⟩ := effects_frameInit Z args.length (q + Z.F + 1) Z.F _
    (Function.update_self cNFP _ m) (fun i hi => (R.beyond hq A₁).pool _ (by omega)) hQ
  generalize effects (frameInit Z.F args.length) _ = m₂ at val A ⊢
  have hNFP : m₂ cNFP = wd W (cStack (q + Z.F + 1)) :=
    A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                       Light.Compiler.Scratch, Light.Compiler.Writable,
                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                       or_false] <;>
                     intros <;>
                   omega)) (Function.update_self _ _ _)
  have A₂ := A₁.trans (A.mono (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                              Light.Compiler.Scratch, Light.Compiler.Writable,
                                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                              or_false] <;>
                                            intros <;>
                                          omega)))
  -- ADDR := NFP + 2
  rw [effect_add cADDR hNFP ((R.beyond hq A₂).pool 2 (by omega)), cStack_succ_add]
  have A₃ := A₂.update (a := cADDR) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                    or_false] <;>
                                                  intros <;>
                                                omega)) (wd W (cStack (q + Z.F)))
  -- the cell at ADDR := ret
  rw [effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega)),
    (R.beyond hq A₃).pool ret hret]
  have A₄ := A₃.update (a := cStack (q + Z.F)) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                               Light.Compiler.Scratch, Light.Compiler.Writable,
                                                               Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                               Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                               Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                               Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                               Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                               Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                               Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                               Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                               Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                               or_false] <;>
                                                             intros <;>
                                                           omega)) (wd W ret)
  have R₄ := R.beyond hq A₄
  -- FP := NFP + 0
  rw [effect_add cFP (by ((repeat
                               (first
                                 | rw [Function.update_self]
                                 |
                                   rw [Function.update_of_ne
                                       (by
                                         (simp only [Set.subset_def, Set.mem_compl_iff,
                                                 Light.Compiler.Constants, Light.Compiler.Scratch,
                                                 Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                 Set.mem_union, Set.mem_insert_iff,
                                                 Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                                 Light.Compiler.mem_temps_iff,
                                                 Light.Compiler.mem_stack_iff,
                                                 Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                                 Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                 Light.Compiler.cONE, Light.Compiler.cZERO,
                                                 Light.Compiler.cNEG, Light.Compiler.cFP,
                                                 Light.Compiler.cADDR, Light.Compiler.cRET,
                                                 Light.Compiler.cRR, Light.Compiler.cNFP,
                                                 Light.Compiler.cD, Light.Compiler.cT,
                                                 Light.Compiler.cPool, Light.Compiler.cStack,
                                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                                 false_or, or_false] <;>
                                               intros <;>
                                             omega))]));
                           (exact hNFP))) R₄.zero, add_zero]
  refine ⟨?_, by repeat
                     (first
                       | rw [Function.update_self]
                       |
                         rw [Function.update_of_ne
                             (by
                               (simp only [Set.subset_def, Set.mem_compl_iff,
                                       Light.Compiler.Constants, Light.Compiler.Scratch,
                                       Light.Compiler.Writable, Light.Compiler.MainFrame,
                                       Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                       Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                       Light.Compiler.cARG1, Light.Compiler.cARG2,
                                       Light.Compiler.cRESULT, Light.Compiler.cONE,
                                       Light.Compiler.cZERO, Light.Compiler.cNEG,
                                       Light.Compiler.cFP, Light.Compiler.cADDR,
                                       Light.Compiler.cRET, Light.Compiler.cRR,
                                       Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                       Light.Compiler.cPool, Light.Compiler.cStack,
                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                       or_false] <;>
                                     intros <;>
                                   omega))]),
    (A₄.mono (Set.union_subset scratch_subset_writable stack_subset_writable)).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                                    or_false] <;>
                                                                                                  intros <;>
                                                                                                omega)) _⟩
  refine R₄.of_agreeOutside ((AgreeOutside.refl {cFP} _).update rfl _) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                     or_false] <;>
                                                                                   intros <;>
                                                                                 omega))
    (Function.update_self _ _ _) (fun i hi => ?_)
    fun a ha => (Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                   Light.Compiler.Scratch, Light.Compiler.Writable,
                                                   Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                   Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                   Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                   Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                   Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                   Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                   Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                   Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                   Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                   or_false] <;>
                                                 intros <;>
                                               omega)) _ _).trans (R₄.mem a ha)
  -- local variable i of the new frame: argument i, or 0
  repeat
    (first
      | rw [Function.update_self]
      |
        rw [Function.update_of_ne
            (by
              (simp only [Set.subset_def, Set.mem_compl_iff,
                      Light.Compiler.Constants, Light.Compiler.Scratch,
                      Light.Compiler.Writable, Light.Compiler.MainFrame,
                      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                      Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                      Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                      Light.Compiler.cARG1, Light.Compiler.cARG2,
                      Light.Compiler.cRESULT, Light.Compiler.cONE,
                      Light.Compiler.cZERO, Light.Compiler.cNEG,
                      Light.Compiler.cFP, Light.Compiler.cADDR,
                      Light.Compiler.cRET, Light.Compiler.cRR,
                      Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                      Light.Compiler.cPool, Light.Compiler.cStack,
                      Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                      or_false] <;>
                    intros <;>
                  omega))])
  rw [val i hi]
  split_ifs with h
  · ((repeat
           (first
             | rw [Function.update_self]
             |
               rw [Function.update_of_ne
                   (by
                     (simp only [Set.subset_def, Set.mem_compl_iff,
                             Light.Compiler.Constants, Light.Compiler.Scratch,
                             Light.Compiler.Writable, Light.Compiler.MainFrame,
                             Set.mem_union, Set.mem_insert_iff,
                             Set.mem_singleton_iff, Set.mem_ofPred_eq,
                             Light.Compiler.mem_temps_iff,
                             Light.Compiler.mem_stack_iff,
                             Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                             Light.Compiler.cARG2, Light.Compiler.cRESULT,
                             Light.Compiler.cONE, Light.Compiler.cZERO,
                             Light.Compiler.cNEG, Light.Compiler.cFP,
                             Light.Compiler.cADDR, Light.Compiler.cRET,
                             Light.Compiler.cRR, Light.Compiler.cNFP,
                             Light.Compiler.cD, Light.Compiler.cT,
                             Light.Compiler.cPool, Light.Compiler.cStack,
                             Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                             false_or, or_false] <;>
                           intros <;>
                         omega))]));
       (exact hargs i h))
  · repeat
       (first
         | rw [Function.update_self]
         |
           rw [Function.update_of_ne
               (by
                 (simp only [Set.subset_def, Set.mem_compl_iff,
                         Light.Compiler.Constants, Light.Compiler.Scratch,
                         Light.Compiler.Writable, Light.Compiler.MainFrame,
                         Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                         Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                         Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                         Light.Compiler.cARG1, Light.Compiler.cARG2,
                         Light.Compiler.cRESULT, Light.Compiler.cONE,
                         Light.Compiler.cZERO, Light.Compiler.cNEG,
                         Light.Compiler.cFP, Light.Compiler.cADDR,
                         Light.Compiler.cRET, Light.Compiler.cRR,
                         Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                         Light.Compiler.cPool, Light.Compiler.cStack,
                         Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                         or_false] <;>
                       intros <;>
                     omega))])
    rw [R.zero]
    simp [frame, List.getElem?_eq_none (not_lt.1 h)]

end Light.Compiler

end
end

section


/-!
# The dispatcher

The machine has no indirect jump.  A return loads the position r to return to into the register RR
and jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, ….  It
arrives at position r after 2 (r + 1) steps and changes no cell but RR (`steps_dispatcher`).

The proof runs one pair of instructions (`steps_dispatcher_pair`) and then counts down: from the
j-th pair on, with k in RR, the machine arrives at position j + k (`steps_dispatcher_from`).
-/

public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

variable {W : ℕ} {code : List Instr} {disp n : ℕ}

/-- The dispatcher for one more position. -/
private theorem dispatcher_succ (n : ℕ) :
    dispatcher (n + 1) = dispatcher n ++ [.sub cRR cRR cONE, .bltz cRR n] := by
  simp [dispatcher, List.range_succ, List.flatMap_append]

/-- Two instructions for each position. -/
theorem length_dispatcher (n : ℕ) : (dispatcher n).length = 2 * n := by
  simp [dispatcher, List.length_flatMap, Nat.mul_comm]

/-- A shorter dispatcher is the beginning of a longer one. -/
private theorem dispatcher_prefix {j n : ℕ} (h : j ≤ n) : dispatcher j <+: dispatcher n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (dispatcher_succ n ▸ List.prefix_append _ _)

/-- The two instructions for the position j. -/
private theorem codeAt_dispatcher {j : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hj : j < n) :
    CodeAt code (disp + 2 * j) [.sub cRR cRR cONE, .bltz cRR j] := by
  have upToPairCode : CodeAt code disp (dispatcher j ++ [.sub cRR cRR cONE, .bltz cRR j]) :=
    dispatcher_succ j ▸ (dispatcher_prefix hj).trans hcode
  exact upToPairCode.right.cast_pos (by rw [length_dispatcher])

/-- The two instructions for the position j, when RR holds v: RR goes down by one, and the machine
goes to j if that is negative and to the next pair if not. -/
private theorem steps_dispatcher_pair {j : ℕ} (hcode : CodeAt code disp (dispatcher n))
    (hj : j < n) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) {v : ℤ} (hv : InRange W (v - 1)) :
    Steps code 2 ⟨disp + 2 * j, Function.update m cRR (wd W v)⟩
      ⟨if v - 1 < 0 then j else disp + 2 * (j + 1), Function.update m cRR (wd W (v - 1))⟩ := by
  have pairCode := codeAt_dispatcher hcode hj
  -- RR := RR - 1
  have run₁ := steps_sub pairCode (Function.update_self cRR (wd W v) m)
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact hone)))
  rw [Function.update_idem] at run₁
  -- if RR < 0 go to j
  exact run₁.trans (steps_bltz pairCode.tail (Function.update_self _ _ _) hv)

/-- The dispatcher from its j-th pair of instructions on, when RR holds k: it arrives at position
j + k.  The positions fit in a word (hn). -/
private theorem steps_dispatcher_from (hcode : CodeAt code disp (dispatcher n))
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1) (k j : ℕ)
    (hjk : j + k < n) :
    Steps code (2 * (k + 1)) ⟨disp + 2 * j, Function.update m cRR (wd W k)⟩
      ⟨j + k, Function.update m cRR (wd W (-1))⟩ := by
  induction k generalizing j with
  | zero =>
    simpa using steps_dispatcher_pair hcode (show j < n by omega) m hone (v := 0)
      (by constructor <;> omega)
  | succ k ih =>
    have run := steps_dispatcher_pair hcode (show j < n by omega) m hone (v := k + 1)
      (by constructor <;> omega)
    rw [if_neg (by omega), add_sub_cancel_right] at run
    rw [Nat.cast_succ]
    -- 2 + 2 (k + 1) steps lead to the position j + 1 + k
    exact ((run.trans (ih (j + 1) (by omega))).cast_count (by ring)).cast_pos (by ring)

/-- From the beginning of the dispatcher, with the position r in RR, the machine arrives at position
r after 2 (r + 1) steps; RR then holds -1, and no other cell has changed.  The positions fit in a
word (hn). -/
theorem steps_dispatcher {r : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hr : r < n)
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1)
    (hRR : m cRR = wd W r) :
    Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m cRR (wd W (-1))⟩ := by
  have := steps_dispatcher_from hcode hn m hone r 0 (by omega)
  rwa [Nat.mul_zero, Nat.add_zero, Nat.zero_add, ← hRR, Function.update_eq_self] at this

end Light.Compiler

end
end

section


/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The number read off the text -/





/-- The outermost frame has room for the result and the two arguments. -/
theorem three_le_frameSize (P : Program) : 3 ≤ frameSize P := le_max_left _ _





/-! ## The parts of the code -/























































































/-! ## Lengths and positions -/









/-- The outermost statement uses the local variables 0, 1, 2. -/
theorem width_mainStmt (p0 : ℕ) : (mainStmt p0).width = 3 := rfl
























section parts

variable (P : Program) (p0 : ℕ) (dec : Bool)














private theorem length_through_dispatcher :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec) ++
      dispatcher (dispPos P dec)).length = 3 * dispPos P dec := by
  rw [List.length_append, length_through_bodiesCode, length_dispatcher]
  omega

/-- The first part is at position 0. -/
theorem codeAt_headCode : CodeAt (compileProgram P p0 dec) 0 (headCode P dec) :=
  (codeAt_self _).left.left.left.left

private theorem codeAt_mainCode : CodeAt (compileProgram P p0 dec) mainPos (mainCode P p0 dec) :=
  (codeAt_self _).left.left.left.right

/-- The outermost statement is at `mainPos`. -/
theorem codeAt_mainStmt :
    CodeAt (compileProgram P p0 dec) mainPos
      (compileStmt (codeLayout P dec) (mainStmt p0) mainPos) :=
  (codeAt_mainCode P p0 dec).left

/-- The code for the verdict follows the outermost statement. -/
theorem codeAt_tailCode :
    CodeAt (compileProgram P p0 dec) (tailPos (frameSize P))
      (tailCode dec (tailPos (frameSize P))) :=
  (codeAt_mainCode P p0 dec).right.cast_pos (by
    simp only [length_compileStmt, size_mainStmt, tailPos, codeLayout])












/-- The start-up code follows the dispatcher. -/
theorem codeAt_startCode :
    CodeAt (compileProgram P p0 dec) (3 * dispPos P dec) (startCode P dec) :=
  (codeAt_self _).right.cast_pos (by rw [length_through_dispatcher, Nat.zero_add])

end parts


















end Light.Compiler

end
end

section


/-!
# The compiler is correct on statements: the simulation theorem

A run of a statement of the light language in c steps is matched by a run of its code in at most
stepsPerStep · c steps of the machine (`sim`).

What never changes (the program, its code, the numbers of `Sizes`, and the facts that the code is in
place and that a frame is wide enough for the text) forms the structure `Setting`.  The situation
before the code of a statement runs is `Start`: the code is at pos, and the memory represents the
state in the frame q, with room on the stack for the calls still allowed.  The situation afterwards
is `Finished`: the machine has reached the position after the code, the memory represents the new
state in the same frame, and only cells that the statement may write have changed.  `Simulates` says
that `Start` leads to `Finished`.

The theorem is an induction on the run, with one lemma for each rule of the semantics: `sim_skip`,
`sim_set`, `sim_store`, `sim_seq`, `sim_iteTrue`, `sim_iteFalse`, `sim_whileFalse`,
`sim_whileTrue`, `sim_call`.  Each of them first takes the code of the statement apart (`codeAt_ite`
and its like say where the parts are) and then runs the parts in turn.  A call has four parts.
Enter (`steps_callEnter`): arguments, new frame, position to return to, jump.  The body: the
induction hypothesis.  Leave (`steps_callLeave`): return sequence and dispatcher.  Store the result
in the caller's variable (`steps_setVar`).

In the proofs S is the setting and B the situation at the start; the other letters are as in the
file on the cells.
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt}
  {args : List Expr}

/-- The code of e, and the two instructions that store T₀ in x. -/
private theorem codeAt_set (h : CodeAt code pos (compileStmt G (.set x e) pos)) :
    CodeAt code pos (compileExpr e 0) ∧
      CodeAt code (pos + e.size) [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)] :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileExpr])⟩

/-- The code of s, and the code of t. -/
private theorem codeAt_seq (h : CodeAt code pos (compileStmt G (.seq s t) pos)) :
    CodeAt code pos (compileStmt G s pos) ∧
      CodeAt code (pos + s.size G.F) (compileStmt G t (pos + s.size G.F)) :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileStmt])⟩

/-- The test, the first branch, the jump over the second branch, the second branch. -/
private theorem codeAt_ite (h : CodeAt code pos (compileStmt G (.ite c s t) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F)
        [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ∧
      CodeAt code (pos + c.size + s.size G.F + 1)
        (compileStmt G t (pos + c.size + s.size G.F + 1)) := by
  rw [compileStmt] at h
  refine ⟨h.left.left.left, h.left.left.right.cast_pos ?_, h.left.right.cast_pos ?_,
    h.right.cast_pos ?_⟩ <;> simp +arith [length_compileCond, length_compileStmt]

/-- The test, the body, the jump back. -/
private theorem codeAt_while (h : CodeAt code pos (compileStmt G (.while c s) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F) [.bltz cNEG pos] := by
  rw [compileStmt] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_compileCond, length_compileStmt]

/-- The arguments and the new frame, the jump to the procedure, and the two instructions that store
the result. -/
private theorem codeAt_call (h : CodeAt code pos (compileStmt G (.call p args x) pos)) :
    CodeAt code pos (argsCode args 0 ++ newFrame G.F args.length (pos + callSize G.F args)) ∧
      CodeAt code (pos + (argsSize args + (2 * G.F + 4))) [.bltz cNEG (G.entry.getD p 0)] ∧
      CodeAt code (pos + callSize G.F args)
        [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET] := by
  rw [compileStmt, callCode] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_argsCode, length_newFrame, callSize]

end layout

/-! ## The setting -/

























/-- At most n machine steps are within the bound for c ≥ 1 steps of the language. -/
private theorem le_stepsPerStep_mul {a c n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) :
    a ≤ stepsPerStep n * c :=
  calc a ≤ stepsPerStep n * 1 := by rw [stepsPerStep]; omega
    _ ≤ stepsPerStep n * c := Nat.mul_le_mul_left _ hc

/-- At most n machine steps, followed by b machine steps that are within the bound for k steps, are
within the bound for c + k steps if c ≥ 1. -/
private theorem add_le_stepsPerStep_mul {a b c k n : ℕ} (h : a ≤ n) (hc : 1 ≤ c)
    (hb : b ≤ stepsPerStep n * k) : a + b ≤ stepsPerStep n * (c + k) :=
  Nat.mul_add _ c k ▸ Nat.add_le_add (le_stepsPerStep_mul h hc) hb

/-- The count for a call whose code is at pos and has size + 2 instructions: size steps to enter, b
for the body, r + 2 (pos + size + 1) to leave, where r is the length of the return sequence, and 2
to store the result.  The cost a of the arguments is not needed. -/
private theorem call_le_stepsPerStep_mul {pos size b r a k n : ℕ} (hpos : pos + (size + 2) ≤ n)
    (hr : r ≤ n) (hb : b ≤ stepsPerStep n * k) :
    size + b + (r + 2 * (pos + size + 1)) + 2 ≤ stepsPerStep n * (a + 2 + k) := by
  rw [Nat.mul_add (stepsPerStep n), Nat.mul_add (stepsPerStep n)]
  have hK : stepsPerStep n * 2 = 4 * n := by rw [stepsPerStep]; omega
  omega

variable {W : ℕ} (S : Setting W)

































variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}

/-- The situation before a part t of the statement runs, in the same frame. -/
private theorem Start.sub (B : Start S d s σ pos q m) {t : Stmt} {pos' : ℕ} {m' : ℤ → BitVec W}
    (hcode : CodeAt S.code pos' (compileStmt S.toCodeLayout t pos'))
    (hpos : pos' + t.size S.F ≤ S.disp) (hw : t.width ≤ S.F) (hσ : σ'.Bounded S.lim)
    (R : Rel S.toSizes σ' q m') : Start S d t σ' pos' q m' :=
  { rel := R, low := B.low, high := B.high, codeAt := hcode, below := hpos, width := hw,
    bounded := hσ, room := B.room }

/-- The room on the stack, seen from the frame of a procedure that is called. -/
private theorem Start.room_succ (B : Start S d s σ pos q m) (hd : d < S.lim.depth) :
    q + S.F + 1 + S.F + (S.F + 1) * (S.lim.depth - (d + 1)) ≤ S.Q := by
  have := B.room
  rw [show S.lim.depth - d = S.lim.depth - (d + 1) + 1 by omega, Nat.mul_succ] at this
  omega

/-- The test of an if or a while that is at pos. -/
private theorem Start.test (B : Start S d s σ pos q m) {c : Cond} {l : ℕ}
    (hcode : CodeAt S.code pos (compileCond c l)) (hw : c.width ≤ S.F) (hs : c.Safe S.lim σ) :
    Decides S.code S.F pos c.size l m (c.Holds σ) :=
  decides_compileCond B.toFramed B.bounded c hcode hw hs

/-! ## Statements without calls -/

/-- skip: no code, no step. -/
private theorem sim_skip : Simulates S d .skip σ σ 0 := fun _ _ m B =>
  ⟨m, 0, { run := Steps.refl _, le := Nat.zero_le _, rel := B.rel, agree := AgreeOutside.refl _ m }⟩

/-- x := e: the code of e leaves the value in T₀, and two instructions store it in x. -/
private theorem sim_set {x : ℕ} {e : Expr} (hs : e.Safe S.lim σ) :
    Simulates S d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) }
      (e.cost + 1) := by
  intro pos q m B
  obtain ⟨hx, he⟩ := Stmt.width_set_le_iff.1 B.width
  obtain ⟨exprCode, setCode⟩ := codeAt_set B.codeAt
  have hpos : pos + (e.size + 2) ≤ S.disp := B.below
  -- T₀ := e
  obtain ⟨val, A⟩ := effects_compileExpr_of_width B.toFramed e 0 he hs (by omega)
  have A₁ := A.mono temps_subset_scratch
  have run₁ := steps_straight _ pos m exprCode (straight_compileExpr e 0)
  rw [length_compileExpr] at run₁
  -- x := T₀
  obtain ⟨m₂, run₂, R₂, A₂⟩ := steps_setVar (B.toFramed.same A₁) hx setCode val (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                                          or_false] <;>
                                                                                                        intros <;>
                                                                                                      omega))
  exact ⟨m₂, _, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := R₂
    agree := (A₁.mono scratch_subset_writable).trans A₂ }⟩

/-- The cell at a := e: the code of a and e leaves the values in T₀ and T₁, and one instruction
stores. -/
private theorem sim_store {a e : Expr} (hsa : a.Safe S.lim σ) (hse : e.Safe S.lim σ)
    (haddr : S.lim.Addr (a.val σ)) :
    Simulates S d (.store a e) σ
      { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } (a.cost + e.cost + 1) := by
  intro pos q m B
  obtain ⟨ha, he⟩ := Stmt.width_store_le_iff.1 B.width
  have hpos : pos + (a.size + e.size + 1) ≤ S.disp := B.below
  -- T₀ := a; T₁ := e
  obtain ⟨m₁, run₁, va, ve, A₁⟩ := steps_pair B.toFramed B.codeAt ha he hsa hse
  -- the cell at T₀ := T₁
  have run₂ := run₁.trans (steps_store (codeAt_after_pair B.codeAt) va (S.inRange_addr haddr))
  rw [ve] at run₂
  exact ⟨_, _, {
    run := run₂.cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := (B.rel.same A₁).setMem B.low haddr _
    agree := (A₁.mono scratch_subset_writable).update (mem_writable_of_addr haddr) _ }⟩

/-- s₁; s₂: the code of s₁, then the code of s₂. -/
private theorem sim_seq {c₁ c₂ : ℕ} (h₁ : Exec S.lim S.P d s₁ σ σ₁ c₁)
    (ih₁ : Simulates S d s₁ σ σ₁ c₁) (ih₂ : Simulates S d s₂ σ₁ σ₂ c₂) :
    Simulates S d (.seq s₁ s₂) σ σ₂ (c₁ + c₂) := by
  intro pos q m B
  obtain ⟨hw₁, hw₂⟩ := Stmt.width_seq_le_iff.1 B.width
  obtain ⟨firstCode, secondCode⟩ := codeAt_seq B.codeAt
  have hpos : pos + (s₁.size S.F + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _ (B.sub firstCode (by omega) hw₁ B.bounded B.rel)
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih₂ _ _ _
    (B.sub secondCode (by omega) hw₂ (h₁.bounded B.bounded) R₁)
  exact ⟨m₂, n₁ + n₂, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := Nat.mul_add _ c₁ c₂ ▸ Nat.add_le_add le₁ le₂
    rel := R₂
    agree := A₁.trans A₂ }⟩

/-- if c then s₁ else s₂, when c holds: the test goes on to the code of s₁, and a jump leads over
the code of s₂. -/
private theorem sim_iteTrue {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (ih : Simulates S d s₁ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, hw₁, -⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, thenCode, jumpCode, -⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the first branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub thenCode (by omega) hw₁ B.bounded (B.rel.same A₀))
  -- the jump over the second branch
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  exact ⟨m₁, n₀ + 1 + n₁, {
    run := (run₂.cast_count (by omega)).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- if c then s₁ else s₂, when c fails: the test jumps to the code of s₂. -/
private theorem sim_iteFalse {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ)
    (ih : Simulates S d s₂ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, -, hw₂⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, -, -, elseCode⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  -- the second branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub elseCode (by omega) hw₂ B.bounded (B.rel.same A₀))
  exact ⟨m₁, n₀ + n₁, {
    run := (run₀.trans run₁).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- while c do s, when c fails: the test jumps to the position after the loop. -/
private theorem sim_whileFalse {c : Cond} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ) :
    Simulates S d (.while c s) σ σ (c.cost + 1) := by
  intro pos q m B
  obtain ⟨hwc, -⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, -, -⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  exact ⟨m₀, n₀, {
    run := run₀.cast_pos (by rw [Stmt.size]; omega)
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := B.rel.same A₀
    agree := A₀.mono scratch_subset_writable }⟩

/-- while c do s, when c holds: the test goes on to the code of s, a jump leads back to the test,
and the loop runs again. -/
private theorem sim_whileTrue {c : Cond} {k₁ k₂ : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (h₁ : Exec S.lim S.P d s σ σ₁ k₁) (ih₁ : Simulates S d s σ σ₁ k₁)
    (ih₂ : Simulates S d (.while c s) σ₁ σ₂ k₂) :
    Simulates S d (.while c s) σ σ₂ (c.cost + 1 + k₁ + k₂) := by
  intro pos q m B
  obtain ⟨hwc, hw⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, bodyCode, jumpCode⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the body
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _
    (B.sub bodyCode (by omega) hw B.bounded (B.rel.same A₀))
  -- the jump back
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  -- the loop again
  obtain ⟨m₃, n₃, run₃, le₃, R₃, A₃⟩ := ih₂ _ _ _
    (B.sub B.codeAt B.below B.width (h₁.bounded B.bounded) R₁)
  exact ⟨m₃, n₀ + 1 + n₁ + n₃, {
    run := (run₂.trans run₃).cast_count (by omega)
    le := Nat.mul_add _ _ k₂ ▸ Nat.add_le_add (add_le_stepsPerStep_mul (by omega) (by omega) le₁)
        le₃
    rel := R₃
    agree := ((A₀.mono scratch_subset_writable).trans A₁).trans A₃ }⟩

/-! ## Calls -/

section call

variable {p x : ℕ} {args : List Expr}

/-- Entering a procedure: the arguments, the new frame with the position to return to, and the jump
to the entry e.  Afterwards the memory represents the state in which the procedure starts, in the
frame q + F + 1, and the stack cell before that frame holds the position after the jump.  Of the
stack, only cells from q + F on have changed. -/
private theorem steps_callEnter (B : Start S d (.call p args x) σ pos q m)
    (hsa : ∀ e ∈ args, e.Safe S.lim σ) (hd : d < S.lim.depth) {e : ℕ}
    (he : S.entry[p]? = some e) :
    ∃ m₂, Steps S.code (callSize S.F args) ⟨pos, m⟩ ⟨e, m₂⟩ ∧
      Rel S.toSizes ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + S.F + 1) m₂ ∧
      m₂ (cStack (q + S.F)) = wd W ((pos + callSize S.F args : ℕ) : ℤ) ∧
      AgreeOutside (Writable S.toSizes (q + S.F)) m m₂ := by
  obtain ⟨-, hlen, hwa⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨frameCode, jumpCode, -⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  rw [List.getD_eq_getElem?_getD, he, Option.getD_some] at jumpCode
  -- the arguments: there are at most F of them, each of width at most F
  obtain ⟨vals, A⟩ := effects_argsCode B.toFramed args 0 hwa hsa (by omega)
  have A₁ := A.mono temps_subset_scratch
  -- the new frame
  obtain ⟨R₂, hret, A₂⟩ := effects_newFrame (B.toFramed.same A₁)
    ((Nat.le_add_right _ _).trans (B.room_succ hd)) args (by simpa using vals)
    (ret := pos + callSize S.F args) (by omega)
  have run₂ := steps_straight _ pos m frameCode
    (List.forall_mem_append.2 ⟨straight_argsCode _ _, straight_newFrame _ _ _⟩)
  rw [effects_append, List.length_append, length_argsCode, length_newFrame] at run₂
  -- the jump
  exact ⟨_, (run₂.trans (steps_jump jumpCode R₂.neg S.inRange_neg_one)).cast_count
    (by rw [callSize]; omega), R₂, hret, (A₁.mono scratch_subset_writable).trans A₂⟩

/-- Leaving a procedure whose frame is q + F + 1, when the stack cell before that frame holds the
position ret: the return sequence and the dispatcher.  The machine arrives at ret; RET holds the
result (local variable 0), FP points to the frame q, and otherwise only scratch cells have
changed. -/
private theorem steps_callLeave (S : Setting W) {ret : ℕ} (R : Rel S.toSizes σ (q + S.F + 1) m)
    (hcode : CodeAt S.code pos (epilogue S.toCodeLayout))
    (hret : m (cStack (q + S.F)) = wd W ret) (hlt : ret < S.disp) (hQ : q + S.F + 1 ≤ S.Q)
    (hF : 0 < S.F) :
    ∃ m', Steps S.code (epilogueSize + 2 * (ret + 1)) ⟨pos, m⟩ ⟨ret, m'⟩ ∧
      m' cFP = wd W (cStack q) ∧ m' cRET = wd W (σ.loc 0) ∧
      AgreeOutside (insert cFP (Scratch S.F)) m m' := by
  have hN := S.offsets_le
  -- RET := the cell at FP, which is local variable 0
  have run₁ := steps_load (i := cRET) hcode R.fp (S.inRange_stack hQ)
  rw [R.loc_zero hF] at run₁
  have A₁ := (AgreeOutside.refl (Scratch S.F) m).update (a := cRET) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                  Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                  Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                  Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                  Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                  Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                  Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                  Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                  Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                  or_false] <;>
                                                                                intros <;>
                                                                              omega)) (wd W (σ.loc 0))
  -- ADDR := FP + 2, the address of the stack cell before the frame
  have run₂ := run₁.trans (steps_add hcode.tail (R.same A₁).fp ((R.same A₁).pool 2 (by omega)))
  rw [cStack_succ_add] at run₂
  have A₂ := A₁.update (a := cADDR) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                    or_false] <;>
                                                  intros <;>
                                                omega)) (wd W (cStack (q + S.F)))
  -- RR := the cell at ADDR, which holds ret
  have run₃ := run₂.trans (steps_load hcode.tail.tail (Function.update_self _ _ _)
    (S.inRange_stack (by omega)))
  rw [A₂.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                            Light.Compiler.Scratch, Light.Compiler.Writable,
                            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                            or_false] <;>
                          intros <;>
                        omega)) hret] at run₃
  have A₃ := A₂.update (a := cRR) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                  Light.Compiler.Scratch, Light.Compiler.Writable,
                                                  Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                  Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                  Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                  Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                  Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                  Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                  Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                  or_false] <;>
                                                intros <;>
                                              omega)) (wd W ret)
  -- FP := FP + 2 (F + 1), the frame of the caller
  have run₄ := run₃.trans (steps_add hcode.tail.tail.tail (R.same A₃).fp ((R.same A₃).pool _ hN))
  rw [Nat.add_assoc q, cStack_add] at run₄
  -- the jump to the dispatcher
  have run₅ := run₄.trans (steps_jump hcode.tail.tail.tail.tail
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact (R.same A₃).neg))) S.inRange_neg_one)
  -- the dispatcher, which leaves -1 in RR
  have run₆ := run₅.trans (steps_dispatcher S.dispatcherAt hlt S.fits.pool_lt _
    (by ((repeat
              (first
                | rw [Function.update_self]
                |
                  rw [Function.update_of_ne
                      (by
                        (simp only [Set.subset_def, Set.mem_compl_iff,
                                Light.Compiler.Constants, Light.Compiler.Scratch,
                                Light.Compiler.Writable, Light.Compiler.MainFrame,
                                Set.mem_union, Set.mem_insert_iff,
                                Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                Light.Compiler.mem_temps_iff,
                                Light.Compiler.mem_stack_iff,
                                Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                Light.Compiler.cONE, Light.Compiler.cZERO,
                                Light.Compiler.cNEG, Light.Compiler.cFP,
                                Light.Compiler.cADDR, Light.Compiler.cRET,
                                Light.Compiler.cRR, Light.Compiler.cNFP,
                                Light.Compiler.cD, Light.Compiler.cT,
                                Light.Compiler.cPool, Light.Compiler.cStack,
                                Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                false_or, or_false] <;>
                              intros <;>
                            omega))]));
          (exact (R.same A₃).one))) (by repeat
                                            (first
                                              | rw [Function.update_self]
                                              |
                                                rw [Function.update_of_ne
                                                    (by
                                                      (simp only [Set.subset_def, Set.mem_compl_iff,
                                                              Light.Compiler.Constants, Light.Compiler.Scratch,
                                                              Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                              Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                                              Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                              Light.Compiler.cARG1, Light.Compiler.cARG2,
                                                              Light.Compiler.cRESULT, Light.Compiler.cONE,
                                                              Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                              Light.Compiler.cFP, Light.Compiler.cADDR,
                                                              Light.Compiler.cRET, Light.Compiler.cRR,
                                                              Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                                              Light.Compiler.cPool, Light.Compiler.cStack,
                                                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                              or_false] <;>
                                                            intros <;>
                                                          omega))])))
  exact ⟨_, run₆, by repeat
                           (first
                             | rw [Function.update_self]
                             |
                               rw [Function.update_of_ne
                                   (by
                                     (simp only [Set.subset_def, Set.mem_compl_iff,
                                             Light.Compiler.Constants, Light.Compiler.Scratch,
                                             Light.Compiler.Writable, Light.Compiler.MainFrame,
                                             Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                             Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                             Light.Compiler.cARG1, Light.Compiler.cARG2,
                                             Light.Compiler.cRESULT, Light.Compiler.cONE,
                                             Light.Compiler.cZERO, Light.Compiler.cNEG,
                                             Light.Compiler.cFP, Light.Compiler.cADDR,
                                             Light.Compiler.cRET, Light.Compiler.cRR,
                                             Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                             Light.Compiler.cPool, Light.Compiler.cStack,
                                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                             or_false] <;>
                                           intros <;>
                                         omega))]), by repeat
                                                         (first
                                                           | rw [Function.update_self]
                                                           |
                                                             rw [Function.update_of_ne
                                                                 (by
                                                                   (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                           Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                           Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                           Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                                                           Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                           Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                           Light.Compiler.cARG1, Light.Compiler.cARG2,
                                                                           Light.Compiler.cRESULT, Light.Compiler.cONE,
                                                                           Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                           Light.Compiler.cFP, Light.Compiler.cADDR,
                                                                           Light.Compiler.cRET, Light.Compiler.cRR,
                                                                           Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                                                           Light.Compiler.cPool, Light.Compiler.cStack,
                                                                           Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                           or_false] <;>
                                                                         intros <;>
                                                                       omega))]),
    ((A₃.mono (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                            Light.Compiler.Scratch, Light.Compiler.Writable,
                            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                            or_false] <;>
                          intros <;>
                        omega))).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                    or_false] <;>
                                                  intros <;>
                                                omega)) _).update (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                              Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                              or_false] <;>
                                                                            intros <;>
                                                                          omega)) _⟩

/-- x := p(args): enter, the body, leave, store the result. -/
private theorem sim_call {body : Stmt} {k : ℕ} (hsa : ∀ e ∈ args, e.Safe S.lim σ)
    (hp : S.P[p]? = some body) (hd : d < S.lim.depth)
    (ih : Simulates S (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k) :
    Simulates S d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
      ((args.map Expr.cost).sum + 2 + k) := by
  intro pos q m B
  obtain ⟨hx, -, -⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨e, he, procCode, hend⟩ := S.bodyAt p body hp
  obtain ⟨-, -, resultCode⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  have hq := B.low
  have hroom := B.room_succ hd
  -- enter
  obtain ⟨m₁, run₁, R₁, hret, A₁⟩ := steps_callEnter B hsa hd he
  -- the body, in the frame q + F + 1
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih e (q + S.F + 1) m₁
    { rel := R₁, low := by omega, high := by omega, codeAt := procCode.left, below := by omega,
      width := S.width body (List.mem_of_getElem? hp),
      bounded := bounded_callFrame B.bounded args hsa, room := hroom }
  -- the body writes the stack only from its frame on, so the position to return to is still there
  have hret₂ := A₂.read (a := cStack (q + S.F)) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                or_false] <;>
                                                              intros <;>
                                                            omega)) hret
  -- leave
  obtain ⟨m₃, run₃, hfp, hres, A₃⟩ := steps_callLeave S R₂
    (procCode.right.cast_pos (by rw [length_compileStmt])) hret₂ (by omega) (by omega)
    (Nat.zero_lt_of_lt hx)
  -- since the call began, the stack has changed only from cell q + F on: the local variables of the
  -- caller are as before, and the memory is as the procedure left it
  have A : AgreeOutside (Writable S.toSizes (q + S.F)) m m₃ :=
    (A₁.trans (A₂.mono (writable_subset_writable (by omega)))).trans
      (A₃.mono (Set.insert_subset (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                or_false] <;>
                                              intros <;>
                                            omega)) scratch_subset_writable))
  have I₃ : Framed S.toSizes ⟨σ.loc, σ'.mem⟩ q m₃ := ⟨R₂.of_agreeOutside A₃ (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                                        Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                                        Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                                        Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                                        Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                                        Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                                        Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                                        Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                                        Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                                        Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                                        Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                                        or_false] <;>
                                                                                                      intros <;>
                                                                                                    omega)) hfp
    (fun y hy => A.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega)) (B.rel.loc y hy))
    fun a ha => A₃.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                      Light.Compiler.Scratch, Light.Compiler.Writable,
                                      Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                      Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                      Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                      Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                      Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                      Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                      Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                      Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                      Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                      or_false] <;>
                                    intros <;>
                                  omega)) (R₂.mem a ha), hq, B.high⟩
  -- store the result
  obtain ⟨m₄, run₄, R₄, A₄⟩ := steps_setVar I₃ hx resultCode hres (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                            Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                            or_false] <;>
                                                                                          intros <;>
                                                                                        omega))
  exact ⟨m₄, _, {
    run := (((run₁.trans run₂).trans run₃).trans run₄).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := call_le_stepsPerStep_mul hpos (by omega) le₂
    rel := R₄
    agree := (A.mono (writable_subset_writable (by omega))).trans A₄ }⟩

end call

/-! ## The theorem -/

/-- **The simulation theorem.**  The code of a statement matches every run of the statement. -/
theorem sim (S : Setting W) {c : ℕ} (h : Exec S.lim S.P d s σ σ' c) :
    Simulates S d s σ σ' c := by
  induction h with
  | skip => exact sim_skip
  | set hs => exact sim_set hs
  | store hsa hse haddr => exact sim_store hsa hse haddr
  | seq h₁ _ ih₁ ih₂ => exact sim_seq h₁ ih₁ ih₂
  | iteTrue hs holds _ ih => exact sim_iteTrue hs holds ih
  | iteFalse hs fails _ ih => exact sim_iteFalse hs fails ih
  | whileFalse hs fails => exact sim_whileFalse hs fails
  | whileTrue hs holds h₁ _ ih₁ ih₂ => exact sim_whileTrue hs holds h₁ ih₁ ih₂
  | call hsa hp hd _ ih => exact sim_call hsa hp hd ih

end Light.Compiler

end
end

section


/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

private theorem effects_headStraight (m : ℤ → BitVec W) :
    effects headStraight m =
      Function.update (Function.update (Function.update m cONE (wd W 1)) cZERO (wd W 0)) cNEG
        (wd W (-1)) := by
  simp only [headStraight, effects_cons, effects_nil]
  rw [effect_one, effect_sub cZERO (by repeat
                                         (first
                                           | rw [Function.update_self]
                                           |
                                             rw [Function.update_of_ne
                                                 (by
                                                   (simp only [Set.subset_def, Set.mem_compl_iff,
                                                           Light.Compiler.Constants, Light.Compiler.Scratch,
                                                           Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                           Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                                           Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                           Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                           Light.Compiler.cARG1, Light.Compiler.cARG2,
                                                           Light.Compiler.cRESULT, Light.Compiler.cONE,
                                                           Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                           Light.Compiler.cFP, Light.Compiler.cADDR,
                                                           Light.Compiler.cRET, Light.Compiler.cRR,
                                                           Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                                           Light.Compiler.cPool, Light.Compiler.cStack,
                                                           Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                           or_false] <;>
                                                         intros <;>
                                                       omega))])) (by repeat
                                                                        (first
                                                                          | rw [Function.update_self]
                                                                          |
                                                                            rw [Function.update_of_ne
                                                                                (by
                                                                                  (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                                          Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                                          Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                                          Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                                                                          Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                          Light.Compiler.cARG1, Light.Compiler.cARG2,
                                                                                          Light.Compiler.cRESULT, Light.Compiler.cONE,
                                                                                          Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                          Light.Compiler.cFP, Light.Compiler.cADDR,
                                                                                          Light.Compiler.cRET, Light.Compiler.cRR,
                                                                                          Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                                                                          Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                          or_false] <;>
                                                                                        intros <;>
                                                                                      omega))])),
    effect_sub cNEG (by repeat
                          (first
                            | rw [Function.update_self]
                            |
                              rw [Function.update_of_ne
                                  (by
                                    (simp only [Set.subset_def, Set.mem_compl_iff,
                                            Light.Compiler.Constants, Light.Compiler.Scratch,
                                            Light.Compiler.Writable, Light.Compiler.MainFrame,
                                            Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                            Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                            Light.Compiler.cARG1, Light.Compiler.cARG2,
                                            Light.Compiler.cRESULT, Light.Compiler.cONE,
                                            Light.Compiler.cZERO, Light.Compiler.cNEG,
                                            Light.Compiler.cFP, Light.Compiler.cADDR,
                                            Light.Compiler.cRET, Light.Compiler.cRR,
                                            Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                            Light.Compiler.cPool, Light.Compiler.cStack,
                                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                            or_false] <;>
                                          intros <;>
                                        omega))])) (by repeat
                                                         (first
                                                           | rw [Function.update_self]
                                                           |
                                                             rw [Function.update_of_ne
                                                                 (by
                                                                   (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                           Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                           Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                           Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                                                           Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                           Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                           Light.Compiler.cARG1, Light.Compiler.cARG2,
                                                                           Light.Compiler.cRESULT, Light.Compiler.cONE,
                                                                           Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                           Light.Compiler.cFP, Light.Compiler.cADDR,
                                                                           Light.Compiler.cRET, Light.Compiler.cRR,
                                                                           Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                                                           Light.Compiler.cPool, Light.Compiler.cStack,
                                                                           Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                           or_false] <;>
                                                                         intros <;>
                                                                       omega))]))]
  rfl

/-- The three registers after the first three instructions. -/
private theorem effects_headStraight_consts (m : ℤ → BitVec W) :
    effects headStraight m cONE = wd W 1 ∧ effects headStraight m cZERO = wd W 0 ∧
      effects headStraight m cNEG = wd W (-1) := by
  rw [effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> repeat
                                (first
                                  | rw [Function.update_self]
                                  |
                                    rw [Function.update_of_ne
                                        (by
                                          (simp only [Set.subset_def, Set.mem_compl_iff,
                                                  Light.Compiler.Constants, Light.Compiler.Scratch,
                                                  Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                  Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                                                  Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                  Light.Compiler.cARG1, Light.Compiler.cARG2,
                                                  Light.Compiler.cRESULT, Light.Compiler.cONE,
                                                  Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                  Light.Compiler.cFP, Light.Compiler.cADDR,
                                                  Light.Compiler.cRET, Light.Compiler.cRR,
                                                  Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                                                  Light.Compiler.cPool, Light.Compiler.cStack,
                                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                  or_false] <;>
                                                intros <;>
                                              omega))])

/-! ## The pool -/

private theorem poolCode_succ (N : ℕ) :
    poolCode (N + 1) = poolCode N ++ [.add (cPool (N + 1)) (cPool N) cONE] := by
  simp [poolCode, List.range_succ]

private theorem agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Pool N) m (effects (poolCode N) m) := by
  refine agreeOutside_effects (l := poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show cPool 0 ∈ Pool N
    (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
            Light.Compiler.Scratch, Light.Compiler.Writable,
            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
            or_false] <;>
          intros <;>
        omega)
  · have := List.mem_range.1 hn
    show cPool (n + 1) ∈ Pool N
    (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
            Light.Compiler.Scratch, Light.Compiler.Writable,
            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
            or_false] <;>
          intros <;>
        omega)

/-- After `poolCode N` the pool holds the numbers 0, …, N. -/
private theorem effects_poolCode (hone : m cONE = wd W 1) (N : ℕ) :
    ∀ n ≤ N, effects (poolCode N) m (cPool n) = wd W n := by
  induction N with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [poolCode, List.range_zero, List.map_nil, effects_cons, effects_nil]
    rw [effect_sub _ hone hone, Function.update_self]
    rfl
  | succ N ih =>
    intro n hn
    rw [poolCode_succ, effects_append, effects_cons, effects_nil,
      effect_add _ (ih N le_rfl) ((agreeOutside_poolCode N m).read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                               Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                               Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                               Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                               Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                               Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                               Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                               Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                               Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                               Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                               Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                               or_false] <;>
                                                                             intros <;>
                                                                           omega)) hone)]
    obtain rfl | hlt := hn.eq_or_lt
    · rw [Function.update_self]
      push_cast
      rfl
    · rw [Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                             Light.Compiler.Scratch, Light.Compiler.Writable,
                                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                             or_false] <;>
                                           intros <;>
                                         omega)), ih n (by omega)]





private theorem agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N) m (poolMem N m) := by
  refine AgreeOutside.trans_union ?_ (agreeOutside_poolCode N _)
  rw [effects_headStraight]
  exact (((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _

/-- The code for the pool leaves the numbers 1, 0, -1 in their registers. -/
private theorem poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    poolMem N m cONE = wd W 1 ∧ poolMem N m cZERO = wd W 0 ∧ poolMem N m cNEG = wd W (-1) := by
  obtain ⟨one, zero, neg⟩ := effects_headStraight_consts m
  have keep := agreeOutside_poolCode N (effects headStraight m)
  exact ⟨keep.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                 Light.Compiler.Scratch, Light.Compiler.Writable,
                                 Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                 Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                 Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                 Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                 Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                 Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                 Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                 Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                 or_false] <;>
                               intros <;>
                             omega)) one, keep.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                or_false] <;>
                                                              intros <;>
                                                            omega)) zero, keep.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                                or_false] <;>
                                                                                              intros <;>
                                                                                            omega)) neg⟩

private theorem poolMem_pool (m : ℤ → BitVec W) {n : ℕ} (hn : n ≤ N) :
    poolMem N m (cPool n) = wd W n :=
  effects_poolCode (effects_headStraight_consts m).1 N n hn

/-! ## The outermost frame -/

private theorem zeroCode_succ (F : ℕ) :
    zeroCode (F + 1) = zeroCode F ++ [.sub (cStack (mainFrame + F)) cONE cONE] := by
  simp [zeroCode, List.range_succ]

/-- The instructions of `zeroCode` write into the outermost frame. -/
private theorem writesIn_zeroCode (F : ℕ) : ∀ i ∈ zeroCode F, WritesIn (MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show cStack (mainFrame + x) ∈ MainFrame F
    (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
            Light.Compiler.Scratch, Light.Compiler.Writable,
            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
            or_false] <;>
          intros <;>
        omega)

/-- The local variables of the outermost frame hold zeros. -/
private theorem effects_zeroCode (hone : m cONE = wd W 1) (F : ℕ) :
    ∀ x < F, effects (zeroCode F) m (cStack (mainFrame + x)) = wd W 0 := by
  induction F with
  | zero => exact fun x hx => absurd hx x.not_lt_zero
  | succ F ih =>
    intro x hx
    have hone' := (agreeOutside_effects (writesIn_zeroCode F) m).read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                  Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                  Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                  Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                  Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                  Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                  Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                  Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                  Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                  Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                  or_false] <;>
                                                                                intros <;>
                                                                              omega)) hone
    rw [zeroCode_succ, effects_append, effects_cons, effects_nil, effect_sub _ hone' hone']
    obtain rfl | hlt := (Nat.lt_succ_iff.1 hx).eq_or_lt
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                             Light.Compiler.Scratch, Light.Compiler.Writable,
                                             Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                             Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                             Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                             Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                             Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                             Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                             Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                             Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                             Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                             or_false] <;>
                                           intros <;>
                                         omega)), ih x hlt]

private theorem agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    AgreeOutside ({cFP} ∪ MainFrame F) m (effects (frameCode F) m) := by
  refine agreeOutside_effects (l := frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show cStack (mainFrame + 1) ∈ _
    (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
            Light.Compiler.Scratch, Light.Compiler.Writable,
            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
            or_false] <;>
          intros <;>
        omega)
  · -- local variable 2 := the second argument
    show cStack (mainFrame + 2) ∈ _
    (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
            Light.Compiler.Scratch, Light.Compiler.Writable,
            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
            or_false] <;>
          intros <;>
        omega)

/-- The code for the outermost frame: FP, then zeros, then the two arguments. -/
private theorem effects_frameCode {i j : ℤ} (hzero : m cZERO = wd W 0)
    (hpool : m (cPool (2 * mainFrame)) = wd W (2 * mainFrame : ℕ)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) (F : ℕ) :
    effects (frameCode F) m =
      Function.update (Function.update
        (effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))))
        (cStack (mainFrame + 1)) (wd W i)) (cStack (mainFrame + 2)) (wd W j) := by
  -- what the last two instructions read has not been written since the beginning
  have read (a : ℤ) (ha : a ∉ MainFrame F) (hfp : a ≠ cFP) :
      effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))) a = m a :=
    ((agreeOutside_effects (writesIn_zeroCode F) _).cell ha).trans (Function.update_of_ne hfp _ _)
  have zero := (read cZERO (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                       or_false] <;>
                                     intros <;>
                                   omega)) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                       or_false] <;>
                                                     intros <;>
                                                   omega))).trans hzero
  have arg1 := (read cARG1 (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                       or_false] <;>
                                     intros <;>
                                   omega)) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                       or_false] <;>
                                                     intros <;>
                                                   omega))).trans hi
  have arg2 := (read cARG2 (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                       or_false] <;>
                                     intros <;>
                                   omega)) (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                       Light.Compiler.Scratch, Light.Compiler.Writable,
                                                       Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                       Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                       Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                       Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                       Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                       Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                       Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                       Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                       or_false] <;>
                                                     intros <;>
                                                   omega))).trans hj
  simp only [frameCode, effects_cons, effects_append, effects_nil]
  -- FP := 0 - 2 mainFrame
  rw [effect_sub cFP hzero hpool, show (0 : ℤ) - (2 * mainFrame : ℕ) = cStack mainFrame from rfl]
  -- after the zeros: local variable 1 := the first argument + 0
  rw [effect_add _ arg1 zero, add_zero]
  -- local variable 2 := the second argument + 0
  rw [effect_add _ (by ((repeat
                             (first
                               | rw [Function.update_self]
                               |
                                 rw [Function.update_of_ne
                                     (by
                                       (simp only [Set.subset_def, Set.mem_compl_iff,
                                               Light.Compiler.Constants, Light.Compiler.Scratch,
                                               Light.Compiler.Writable, Light.Compiler.MainFrame,
                                               Set.mem_union, Set.mem_insert_iff,
                                               Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                               Light.Compiler.mem_temps_iff,
                                               Light.Compiler.mem_stack_iff,
                                               Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                               Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                               Light.Compiler.cONE, Light.Compiler.cZERO,
                                               Light.Compiler.cNEG, Light.Compiler.cFP,
                                               Light.Compiler.cADDR, Light.Compiler.cRET,
                                               Light.Compiler.cRR, Light.Compiler.cNFP,
                                               Light.Compiler.cD, Light.Compiler.cT,
                                               Light.Compiler.cPool, Light.Compiler.cStack,
                                               Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                               false_or, or_false] <;>
                                             intros <;>
                                           omega))]));
                         (exact arg2))) (by ((repeat
                                                  (first
                                                    | rw [Function.update_self]
                                                    |
                                                      rw [Function.update_of_ne
                                                          (by
                                                            (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                    Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                    Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                    Set.mem_union, Set.mem_insert_iff,
                                                                    Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                                                    Light.Compiler.mem_temps_iff,
                                                                    Light.Compiler.mem_stack_iff,
                                                                    Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                                                    Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                    Light.Compiler.cONE, Light.Compiler.cZERO,
                                                                    Light.Compiler.cNEG, Light.Compiler.cFP,
                                                                    Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                    Light.Compiler.cRR, Light.Compiler.cNFP,
                                                                    Light.Compiler.cD, Light.Compiler.cT,
                                                                    Light.Compiler.cPool, Light.Compiler.cStack,
                                                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                                                    false_or, or_false] <;>
                                                                  intros <;>
                                                                omega))]));
                                              (exact zero))), add_zero]

/-! ## The memory in which the outermost statement starts -/





private theorem startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    startMem F N m = effects (frameCode F) (poolMem N m) := effects_append _ _ _

/-- The start-up code changes only the registers for 1, 0, -1, the pool, FP and the outermost
frame. -/
theorem agreeOutside_startMem (h3 : 3 ≤ F) (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N ∪ ({cFP} ∪ MainFrame F)) m (startMem F N m) :=
  startMem_eq F N m ▸ (agreeOutside_poolMem N m).trans_union (agreeOutside_frameCode h3 _)

/-- After the start-up code the memory represents the state in which the outermost statement
starts: the local variables 1 and 2 hold the two arguments, all others 0.  Nothing is assumed about
the cells below -2 of the initial memory. -/
theorem rel_startMem (Z : Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = wd W (μ a)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) :
    Rel Z ⟨frame [0, i, j], μ⟩ mainFrame (startMem Z.F Z.disp m) := by
  obtain ⟨one, zero, neg⟩ := poolMem_consts Z.disp m
  have keep₁ := agreeOutside_poolMem Z.disp m
  have keep₂ := agreeOutside_frameCode h3 (poolMem Z.disp m)
  have written := effects_frameCode zero (poolMem_pool m hpool) (keep₁.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                          or_false] <;>
                                                                                        intros <;>
                                                                                      omega)) hi)
    (keep₁.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                              Light.Compiler.Scratch, Light.Compiler.Writable,
                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                              or_false] <;>
                            intros <;>
                          omega)) hj) Z.F
  have zeros (x : ℕ) (hx : x < Z.F) (h1 : x ≠ 1) (h2 : x ≠ 2) :
      effects (frameCode Z.F) (poolMem Z.disp m) (cStack (mainFrame + x)) = wd W 0 := by
    rw [written, Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                   Light.Compiler.Scratch, Light.Compiler.Writable,
                                                   Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                   Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                   Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                   Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                   Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                   Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                   Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                   Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                   Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                   or_false] <;>
                                                 intros <;>
                                               omega)), Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                          or_false] <;>
                                                                                        intros <;>
                                                                                      omega))]
    exact effects_zeroCode (by ((repeat
                                     (first
                                       | rw [Function.update_self]
                                       |
                                         rw [Function.update_of_ne
                                             (by
                                               (simp only [Set.subset_def, Set.mem_compl_iff,
                                                       Light.Compiler.Constants, Light.Compiler.Scratch,
                                                       Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                       Set.mem_union, Set.mem_insert_iff,
                                                       Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                                       Light.Compiler.mem_temps_iff,
                                                       Light.Compiler.mem_stack_iff,
                                                       Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                                       Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                       Light.Compiler.cONE, Light.Compiler.cZERO,
                                                       Light.Compiler.cNEG, Light.Compiler.cFP,
                                                       Light.Compiler.cADDR, Light.Compiler.cRET,
                                                       Light.Compiler.cRR, Light.Compiler.cNFP,
                                                       Light.Compiler.cD, Light.Compiler.cT,
                                                       Light.Compiler.cPool, Light.Compiler.cStack,
                                                       Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                                       false_or, or_false] <;>
                                                     intros <;>
                                                   omega))]));
                                 (exact one))) Z.F x hx
  rw [startMem_eq]
  exact {
    one := keep₂.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega)) one
    zero := keep₂.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                     or_false] <;>
                                   intros <;>
                                 omega)) zero
    neg := keep₂.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega)) neg
    pool := fun n hn => keep₂.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                 Light.Compiler.Scratch, Light.Compiler.Writable,
                                                 Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                 Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                 Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                 Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                 Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                 Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                 Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                 Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                 Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                 or_false] <;>
                                               intros <;>
                                             omega)) (poolMem_pool m hn)
    fp := by
      rw [written, Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                     or_false] <;>
                                                   intros <;>
                                                 omega)), Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                            Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                            Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                            Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                            Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                            Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                            Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                            Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                            Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                            Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                            Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                            or_false] <;>
                                                                                          intros <;>
                                                                                        omega)),
        (agreeOutside_effects (writesIn_zeroCode Z.F) _).cell (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                          Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                          Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                          Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                          Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                          Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                          Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                          Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                          Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                          or_false] <;>
                                                                        intros <;>
                                                                      omega)), Function.update_self]
    loc := fun x hx => match x with
      | 0 => zeros 0 hx (by omega) (by omega)
      | 1 => by rw [written, Function.update_of_ne (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                               Light.Compiler.Scratch, Light.Compiler.Writable,
                                                               Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                               Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                               Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                               Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                               Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                               Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                               Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                               Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                               Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                               or_false] <;>
                                                             intros <;>
                                                           omega))]; exact Function.update_self ..
      | 2 => by rw [written]; exact Function.update_self ..
      | x + 3 => zeros (x + 3) hx (by omega) (by omega)
    mem := fun a ha => keep₂.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                Light.Compiler.Scratch, Light.Compiler.Writable,
                                                Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                or_false] <;>
                                              intros <;>
                                            omega)) (keep₁.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                              Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                              Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                              Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                              Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                              Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                              Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                              Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                              Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                              Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                              Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                              or_false] <;>
                                                                            intros <;>
                                                                          omega)) (hm a ha)) }

/-! ## The run from the first instruction to the outermost statement -/

private theorem straight_headStraight : ∀ i ∈ headStraight, Straight i := by
  simp [headStraight, Straight]

private theorem straight_startStraight (F N : ℕ) : ∀ i ∈ startStraight F N, Straight i := by
  simp [startStraight, poolCode, frameCode, zeroCode, Straight, or_imp, forall_and]

private theorem length_startStraight (F N : ℕ) : (startStraight F N).length = N + F + 4 := by
  simp +arith [startStraight, poolCode, frameCode, zeroCode]

/-- From the first instruction to the outermost statement. -/
theorem steps_start (P : Program) (p0 : ℕ) (dec : Bool) (hneg : InRange W (-1))
    (m : ℤ → BitVec W) :
    Steps (compileProgram P p0 dec) (dispPos P dec + frameSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (frameSize P) (dispPos P dec) m⟩ := by
  have head := codeAt_headCode P p0 dec
  have start := codeAt_startCode P p0 dec
  obtain ⟨-, -, neg₀⟩ := effects_headStraight_consts m
  obtain ⟨-, -, neg⟩ := poolMem_consts (dispPos P dec) m
  have neg₁ : startMem (frameSize P) (dispPos P dec) m cNEG = wd W (-1) := by
    rw [startMem_eq, (agreeOutside_frameCode (three_le_frameSize P) _).cell (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                                                                        Light.Compiler.Scratch, Light.Compiler.Writable,
                                                                                        Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                                                                        Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                                                                        Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                                                                        Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                                        Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                                                                        Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                                        Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                                                                        Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                                                                        Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                                                                        or_false] <;>
                                                                                      intros <;>
                                                                                    omega)), neg]
  -- 1, 0, -1; jump to the start-up code; the start-up code; jump back
  refine ((((steps_straight _ 0 m head.left straight_headStraight).trans
    (steps_jump head.right neg₀ hneg)).trans
    (steps_straight _ _ _ start.left (straight_startStraight _ _))).trans
    (steps_jump start.right neg₁ hneg)).cast_count ?_
  rw [length_startStraight, show headStraight.length = 3 from rfl]
  omega

end Light.Compiler

end
end

section


/-!
# The compiler is correct on whole programs

`compileProgram_correct`: if the call of procedure p0 of the light program P ends after c
steps, the compiled program gives its verdict within `ramSteps P dec c` = c₀ + K c steps, where c₀
and K depend on the text of P (and on dec) only.  If the memory of the machine held the memory of
the light program and the two arguments before (`Input`), it holds the final memory afterwards, with
the result in the cell -3 (`Outcome`).

The run of the machine has three parts.

1. The start-up code (`steps_start`) leads to a memory that represents the first state
   (`rel_startMem`).
2. The outermost statement is the call of p0.  The compiled program satisfies what the simulation
   theorem assumes (`setting`, `start_mainStmt`), so `sim` gives a run of at most K c steps to a
   memory that represents the last state.
3. The code that follows copies the result to the cell -3 and gives the verdict (`steps_tail`).

Each part comes with the set of cells that it may change.  The cells below `-lowCell` and the cells
from `lim.space` on are in none of the three sets (`not_mem_of_far`), and neither are the cells -1
and -2.

The notions of the compiler and of its proof are in the namespace `Light.Compiler`.  The statements
about programs name four of them, which are in `Light`: `compileProgram`, `mainStmt`, `verdictOf`,
`ramSteps`.  The passage to the notions of the word RAM also uses `compileProgram_correct` with
`Fits`, `Holds`, `Input` and `Outcome`, the cells `cARG1`, `cARG2`, `cRESULT`, and the numbers
`startCost`, `stepsPerStep`, `dispPos`, `frameSize`, `stackCells`, `lowCell`.
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr exec)

variable {W : ℕ}

/-! ## The verdict -/













/-- The code that follows the outermost statement gets there in at most three steps. -/
private theorem steps_tail {code : List Instr} {pos : ℕ} {dec : Bool}
    (hcode : CodeAt code pos (tailCode dec pos)) {m : ℤ → BitVec W} {r : ℤ}
    (hres : m (cStack mainFrame) = wd W r) (hzero : m cZERO = wd W 0) (hr : InRange W (-r)) :
    ∃ (n : ℕ) (cfg : Cfg W), n ≤ 3 ∧ Steps code n ⟨pos, m⟩ cfg ∧ Verdict code dec r m cfg := by
  -- the cell for the result := the result
  have copy : Steps code 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m cRESULT (wd W r)⟩ :=
    add_zero r ▸ steps_add hcode hres hzero
  cases dec with
  | false =>
    -- accept
    have read : Function.update m cRESULT (wd W r) cRESULT = wd W r := Function.update_self ..
    exact ⟨1, _, by omega, copy, step_accept hcode.tail.head, read,
      (AgreeOutside.refl _ m).update (by simp) _⟩
  | true =>
    have rest : CodeAt code (pos + 1)
      [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept] := hcode.tail
    -- D := 0 - the result; go to accept if D < 0; reject
    have run := (copy.trans (steps_sub rest (by ((repeat
                                                      (first
                                                        | rw [Function.update_self]
                                                        |
                                                          rw [Function.update_of_ne
                                                              (by
                                                                (simp only [Set.subset_def, Set.mem_compl_iff,
                                                                        Light.Compiler.Constants, Light.Compiler.Scratch,
                                                                        Light.Compiler.Writable, Light.Compiler.MainFrame,
                                                                        Set.mem_union, Set.mem_insert_iff,
                                                                        Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                                                        Light.Compiler.mem_temps_iff,
                                                                        Light.Compiler.mem_stack_iff,
                                                                        Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                                                        Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                                                        Light.Compiler.cONE, Light.Compiler.cZERO,
                                                                        Light.Compiler.cNEG, Light.Compiler.cFP,
                                                                        Light.Compiler.cADDR, Light.Compiler.cRET,
                                                                        Light.Compiler.cRR, Light.Compiler.cNFP,
                                                                        Light.Compiler.cD, Light.Compiler.cT,
                                                                        Light.Compiler.cPool, Light.Compiler.cStack,
                                                                        Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                                                        false_or, or_false] <;>
                                                                      intros <;>
                                                                    omega))]));
                                                  (exact hzero)))
      (by ((repeat
                (first
                  | rw [Function.update_self]
                  |
                    rw [Function.update_of_ne
                        (by
                          (simp only [Set.subset_def, Set.mem_compl_iff,
                                  Light.Compiler.Constants, Light.Compiler.Scratch,
                                  Light.Compiler.Writable, Light.Compiler.MainFrame,
                                  Set.mem_union, Set.mem_insert_iff,
                                  Set.mem_singleton_iff, Set.mem_ofPred_eq,
                                  Light.Compiler.mem_temps_iff,
                                  Light.Compiler.mem_stack_iff,
                                  Light.Compiler.mem_pool_iff, Light.Compiler.cARG1,
                                  Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                  Light.Compiler.cONE, Light.Compiler.cZERO,
                                  Light.Compiler.cNEG, Light.Compiler.cFP,
                                  Light.Compiler.cADDR, Light.Compiler.cRET,
                                  Light.Compiler.cRR, Light.Compiler.cNFP,
                                  Light.Compiler.cD, Light.Compiler.cT,
                                  Light.Compiler.cPool, Light.Compiler.cStack,
                                  Light.Compiler.mainFrame, ne_eq, true_or, or_true,
                                  false_or, or_false] <;>
                                intros <;>
                              omega))]));
            (exact hres))))).trans
      (steps_bltz rest.tail (Function.update_self ..) (by rwa [zero_sub]))
    have keep : AgreeOutside {cRESULT, cD} m
        (Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r))) :=
      ((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _
    have read : Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r)) cRESULT =
        wd W r := by
      repeat
        (first
          | rw [Function.update_self]
          |
            rw [Function.update_of_ne
                (by
                  (simp only [Set.subset_def, Set.mem_compl_iff,
                          Light.Compiler.Constants, Light.Compiler.Scratch,
                          Light.Compiler.Writable, Light.Compiler.MainFrame,
                          Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
                          Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                          Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                          Light.Compiler.cARG1, Light.Compiler.cARG2,
                          Light.Compiler.cRESULT, Light.Compiler.cONE,
                          Light.Compiler.cZERO, Light.Compiler.cNEG,
                          Light.Compiler.cFP, Light.Compiler.cADDR,
                          Light.Compiler.cRET, Light.Compiler.cRR,
                          Light.Compiler.cNFP, Light.Compiler.cD, Light.Compiler.cT,
                          Light.Compiler.cPool, Light.Compiler.cStack,
                          Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                          or_false] <;>
                        intros <;>
                      omega))])
    by_cases hpos : 0 < r
    · rw [if_pos (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_accept rest.tail.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩
    · rw [if_neg (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_reject rest.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩

/-! ## Time and space of the compiled program -/




















private theorem frame_le_stackCells (P : Program) (lim : Limits) :
    mainFrame + frameSize P + 1 ≤ stackCells P lim := by
  have := Nat.le_mul_of_pos_right (frameSize P + 1) (show 0 < lim.depth + 1 by omega)
  unfold stackCells
  omega

/-! ## The setting of the simulation theorem -/

section setting

variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}



















variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))

/-- The outermost statement is at `mainPos` and runs in the frame `mainFrame`. -/
private theorem start_mainStmt {σ : State} {m : ℤ → BitVec W} (hσ : σ.Bounded lim)
    (R : Rel (setting P p0 dec hfit).toSizes σ mainFrame m) :
    Start (setting P p0 dec hfit) 0 (mainStmt p0) σ mainPos mainFrame m where
  rel := R
  low := by decide
  high := (Nat.le_succ _).trans (frame_le_stackCells P lim)
  codeAt := codeAt_mainStmt P p0 dec
  below := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [size_mainStmt, setting, codeLayout, mainPos]
    omega
  width := (width_mainStmt p0).trans_le (three_le_frameSize P)
  bounded := hσ
  room := by
    simp only [setting, codeLayout, stackCells, Nat.sub_zero, Nat.mul_succ]
    omega

/-- The cells below `-lowCell` and the cells from `lim.space` on are not among those that the
start-up code, the outermost statement or the code for the verdict may change. -/
private theorem not_mem_of_far {a : ℤ}
    (ha : a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a) :
    a ∉ Constants (dispPos P dec) ∪ ({cFP} ∪ MainFrame (frameSize P)) ∪
      Writable (setting P p0 dec hfit).toSizes mainFrame ∪ {cRESULT, cD} := by
  have hframe := frame_le_stackCells P lim
  have htemps := two_mul_frameSize_add_le_dispPos P dec
  have hstack : 2 * stackCells P lim ≤ lowCell P dec lim := le_max_left _ _
  have hpool : 25 + 4 * dispPos P dec ≤ lowCell P dec lim := le_max_right _ _
  simp only [Writable, setting, codeLayout]
  rcases ha with ha | ha <;> (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                     Light.Compiler.Scratch, Light.Compiler.Writable,
                                     Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                     Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                     Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                     Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                     Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                     Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                     Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                     Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                     Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                     or_false] <;>
                                   intros <;>
                                 omega)

end setting

/-! ## The theorem -/































/-- **The compiler is correct.**  Let the call of procedure p0 of the program P on the arguments i,
j and the memory μ end after c steps within the limits, and let the word size fit the limits.  Then
the compiled program, started on any memory whose cells `a ≥ 0` hold the words of μ and whose
cells -1 and -2 hold i and j, gives its verdict within `startCost + stepsPerStep · c` steps.  Then
the cell -3 holds the result of the procedure and the cells `a ≥ 0` hold the final memory.  The
cells -1 and -2, the cells below `-lowCell` and the cells from `lim.space` on are unchanged.  The
two constants of the time depend on the text of P and on dec only. -/
theorem compileProgram_correct {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : State} {c : ℕ} {m : ℤ → BitVec W}
    (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, i, j], μ⟩ σ' c)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) (hm : Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, exec (compileProgram P p0 dec) (ramSteps P dec c) 0 m
        = some (verdictOf dec (σ'.loc 0), m') ∧ Outcome lim P dec m σ' m' := by
  have hF := three_le_frameSize P
  have hdisp := two_mul_frameSize_add_le_dispPos P dec
  have hσ : State.Bounded lim ⟨frame [0, i, j], μ⟩ :=
    bounded_frame (by simp [hm.arg1_le, hm.arg2_le, (abs_nonneg i).trans hm.arg1_le]) hm.bounded
  have hσ' := h.bounded hσ
  -- the start-up code
  have run₁ := steps_start P p0 dec (setting P p0 dec hfit).inRange_neg_one m
  have keep₁ := agreeOutside_startMem hF (dispPos P dec) m
  -- the outermost statement
  obtain ⟨m', n, fin⟩ := sim (setting P p0 dec hfit) h mainPos mainFrame _ (start_mainStmt hfit hσ
    (rel_startMem _ hF (by simp only [setting, codeLayout, mainFrame]; omega)
      (fun a _ => hm.rep a) hm.arg1 hm.arg2))
  have hn : n ≤ stepsPerStep (dispPos P dec) * c := fin.le
  have run₂ := fin.run.cast_pos (p' := tailPos (frameSize P))
    (by simp only [tailPos, size_mainStmt, setting, codeLayout])
  -- the verdict
  obtain ⟨k, cfg, hk, run₃, tail⟩ := steps_tail (codeAt_tailCode P p0 dec)
    (fin.rel.loc 0 (show 0 < frameSize P by omega)) fin.rel.zero
    (hfit.inRange (by rw [abs_neg]; exact hσ'.1 0))
  have run := (run₁.trans run₂).trans run₃
  have keep := (keep₁.trans_union fin.agree).trans_union tail.agree
  have far (a : ℤ) ha : cfg.mem a = m a := keep.cell (not_mem_of_far hfit ha)
  refine ⟨cfg.mem, exec_mono (c := ⟨0, m⟩) (exec_of_steps run tail.verdict) ?_,
    { holds := ⟨fun a => ?_, hσ'.2⟩
      result := tail.result ▸ toInt_wd (hfit.inRange (hσ'.1 0))
      arg1 := keep.cell (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega))
      arg2 := keep.cell (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                    Light.Compiler.Scratch, Light.Compiler.Writable,
                                    Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                    Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                    Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                    Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                    Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                    Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                    Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                    Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                    Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                    or_false] <;>
                                  intros <;>
                                omega))
      far := far }⟩
  · simp only [ramSteps, startCost]
    omega
  · by_cases ha : a < lim.space
    · exact tail.agree.read (by (simp only [Set.subset_def, Set.mem_compl_iff, Light.Compiler.Constants,
                                         Light.Compiler.Scratch, Light.Compiler.Writable,
                                         Light.Compiler.MainFrame, Set.mem_union, Set.mem_insert_iff,
                                         Set.mem_singleton_iff, Set.mem_ofPred_eq, Light.Compiler.mem_temps_iff,
                                         Light.Compiler.mem_stack_iff, Light.Compiler.mem_pool_iff,
                                         Light.Compiler.cARG1, Light.Compiler.cARG2, Light.Compiler.cRESULT,
                                         Light.Compiler.cONE, Light.Compiler.cZERO, Light.Compiler.cNEG,
                                         Light.Compiler.cFP, Light.Compiler.cADDR, Light.Compiler.cRET,
                                         Light.Compiler.cRR, Light.Compiler.cNFP, Light.Compiler.cD,
                                         Light.Compiler.cT, Light.Compiler.cPool, Light.Compiler.cStack,
                                         Light.Compiler.mainFrame, ne_eq, true_or, or_true, false_or,
                                         or_false] <;>
                                       intros <;>
                                     omega)) (fin.rel.mem a ha)
    · rw [far _ (Or.inr (by exact_mod_cast not_lt.1 ha)), h.mem_outside a (not_lt.1 ha)]
      exact hm.rep a

end Light.Compiler

end
end

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam


































/-- The bound is positive. -/
theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)



































/-- A power of two times the bound is a bound of the same form. -/
theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]









end Light

end
end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/






























/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/



































/-- **A solver meets the specification that its task prescribes**, in every program that begins with
its program. -/
theorem Solves.meets {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : _root_.Light.Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ} (x : task.Inst) {μ : ℕ → ℤ}
    (fr : ℕ) (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩












































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/
























































/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : Problem} {P : List Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : _root_.ThreeSumApsp.WordRam.Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : _root_.ThreeSumApsp.WordRam.Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩



















/-! ## Bounds up to a constant -/

































/-! ## Bounds in one size -/


































end ThreeSumApsp.WordRam

end
end

section


/-!
# From runs of light programs to the running-time notions of the word RAM

`Solves` says what it means that a program of the word RAM solves a problem within a time bound, and
`IsDataStructure` that two programs form a data structure.  This file gives the corresponding
notions for light programs (`ProgramSolves`, `ProgramIsDataStructure`; what they ask on one instance
are the structures `ProgramSolvesAt` and `ProgramIsDataStructureAt`), which speak only about `Exec`,
and proves that the compiled programs satisfy the notions of the word RAM with time C · T + C, where
C depends on the compiled program only (`solves_of_programSolves`, `isDataStructure_of_program`).

1. **Word size.**  The limits of the run are polynomial in the parameters of the instance (`Small`),
   so they fit every admissible word size of slope `slopeOf` (`fits_of_small`).
2. **Time and space.**  c steps become at most C · c + C steps (`ramSteps_le`); calls nested d deep
   reach at most C · d + C cells below 0 (`lowCell_le`).
3. **Runs.**  Each run is one use of `compileProgram_correct`.  A solver is one run from the initial
   memory (`input_loadWords`).  A data structure is one such run for the preprocessing and then an
   induction on the list of queries, each of them one run (`serves_of_program`).
4. **From specifications.**  The runs that the two notions ask for come from specifications of the
   procedures (`Meets.main`, `AnswersQueries.of_meets`).
5. **The additive constant.**  If T ≥ 1, the bound C · (A · T) + C is at most C (A + 1) · T
   (`solves_of_programSolves_scaled`, `isDataStructure_of_program_scaled`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light

open ThreeSumApsp Compiler
open EndStatement (exec loadWords)

/-! ## The notion for light programs -/












































/-! ## The word size -/













/-- The word size fits the limits if the limits, the largest number N of the pool and the number Q
of cells of the stack, with the factors of `Fits`, are below a number B ≤ 2^W. -/
private theorem fits_of_lt {W : ℕ} {lim : Limits} {N Q B : ℕ} (hB : B ≤ 2 ^ W)
    (hword : 2 * (2 * lim.word + 2) < (B : ℤ)) (hspace : 2 * lim.space < B) (hstack : 4 * Q < B)
    (hpool : 2 * N < B) : Fits W lim N Q := by
  have hB' : (B : ℤ) ≤ (2 : ℤ) ^ W := by exact_mod_cast hB
  constructor <;> omega

/-- Limits that are polynomial in the parameters fit every admissible word size. -/
theorem fits_of_small {W s k r b : ℕ} {params : List ℕ} {lim : Limits} (P : Program) (dec : Bool)
    (h : Small s k params lim) (hadm : Admissible b params W) (hr : params.length ≤ r)
    (hb : slopeOf P dec s k r ≤ b) : Fits W lim (dispPos P dec) (stackCells P lim) := by
  have hword := h.word
  have hspace := h.space
  have hdepth := h.depth
  set pb := polyBound s k params with hpb
  have hpb_pos : 1 ≤ pb := one_le_polyBound s k params
  -- the text's constant times the polynomial is below 2^W
  have hB : 2 ^ textBoundBits P dec * pb ≤ 2 ^ W := by
    rw [hpb, polyBound_mul]
    exact polyBound_le hadm hr (by unfold slopeOf at hb; omega)
  have hlt : textBound P dec * pb < 2 ^ textBoundBits P dec * pb :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) hpb_pos
  have htext : textBound P dec * pb
      = 32 * pb + 8 * ((frameSize P + 1) * pb) + 2 * (dispPos P dec * pb) := by
    unfold textBound; ring
  -- and each of the four numbers is below the text's constant times the polynomial
  have hstack : (frameSize P + 1) * (lim.depth + 1) ≤ 2 * ((frameSize P + 1) * pb) :=
    (Nat.mul_le_mul_left _ (by omega : lim.depth + 1 ≤ 2 * pb)).trans_eq (by ring)
  have hpool : dispPos P dec ≤ dispPos P dec * pb := Nat.le_mul_of_pos_right _ hpb_pos
  refine fits_of_lt hB ?_ ?_ ?_ ?_
  · -- 2 (2 word + 2) ≤ 4 pb + 4 ≤ 8 pb
    have : ((8 * pb : ℕ) : ℤ) < ((2 ^ textBoundBits P dec * pb : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 8 * pb < 2 ^ textBoundBits P dec * pb)
    omega
  · -- 2 space ≤ 2 pb
    omega
  · -- 4 (4 + (F + 1) (depth + 1)) ≤ 16 pb + 8 (F + 1) pb
    unfold stackCells mainFrame
    omega
  · -- 2 N ≤ 2 N pb
    omega

/-! ## Time and space -/










/-- The time of a compiled program. -/
theorem ramSteps_le (P : Program) (dec : Bool) (c : ℕ) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * (c : ℝ) + timeConst P dec := by
  have hstart : startCost P dec ≤ timeConst P dec := by unfold timeConst; omega
  have hsim : stepsPerStep (dispPos P dec) ≤ timeConst P dec := by unfold timeConst; omega
  have : ramSteps P dec c ≤ timeConst P dec * c + timeConst P dec :=
    (Nat.add_comm _ _).trans_le (Nat.add_le_add (Nat.mul_le_mul_right c hsim) hstart)
  exact_mod_cast this

private theorem ramSteps_le_of_le (P : Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * T + timeConst P dec :=
  (ramSteps_le P dec c).trans (by gcongr)





































/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}

/-- The initial memory holds the input, and zeros in the cells of the two arguments. -/
theorem input_loadWords (W : ℕ) {ws : List ℤ} (h0 : 0 ≤ lim.word) (h : ∀ v ∈ ws, |v| ≤ lim.word) :
    Input lim (memOf ws) 0 0 (loadWords W ws) where
  rep := loadWords_mem_nat W ws
  bounded := AbsLe.abs_getD_le h0 h
  arg1 := loadWords_mem_neg W ws (by decide)
  arg2 := loadWords_mem_neg W ws (by decide)
  arg1_le := by simpa using h0
  arg2_le := by simpa using h0

/-- Reading the output: a cell of a memory that holds μ, as a signed word. -/
theorem Compiler.Holds.output {c : ℤ → BitVec W} (h : Holds W lim μ c) {N Q : ℕ}
    (hfit : Fits W lim N Q) (off i : ℕ) : WordRam.output c off i = μ (off + i) := by
  rw [WordRam.output, ← Nat.cast_add, h.rep]
  exact toInt_wd (hfit.inRange (h.bounded _))

end run

/-! ## Solvers -/

/-- **The compiled program solves the problem on the word RAM**, within C · T + C steps, C depending
on the compiled program only. -/
theorem solves_of_programSolves {prob : Problem} {P : Program} {p0 : ℕ} {dec : Bool} {s k r : ℕ}
    {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} (h : ProgramSolves prob P p0 dec s k dom T)
    (hr : ∀ x, (prob.params x).length ≤ r) :
    _root_.ThreeSumApsp.WordRam.Solves prob (compileProgram P p0 dec) (slopeOf P dec s k r) dom
      fun x => (timeConst P dec : ℝ) * T x + timeConst P dec := by
  intro x hx W hadm
  obtain ⟨lim, σ', c, h⟩ := h x hx
  have hfit := fits_of_small P dec h.small hadm (hr x) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct h.run hfit (input_loadWords W h.small.nonneg h.input_fits)
  refine ⟨_, _, cfg, ramSteps_le_of_le P dec h.time, hrun, ?_⟩
  rw [show output cfg (prob.input x).length = fun i => σ'.mem ((prob.input x).length + i) from
    funext (out.holds.output hfit _)]
  exact h.answer

/-! ## The two-stage data structure -/








































































































/-! ## Absorbing the additive constant -/



































end Light

end
end

section


/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/

@[expose] public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam

variable {lim : Limits} {P : Program} {d : ℕ}




















/-- The loop that is written out κ times turns U = 1 into U = n^κ. -/
theorem pow_spec {n : ℕ} (hn : 1 ≤ n) (a : ℤ) (μ : ℕ → ℤ) : ∀ κ : ℕ, ((n ^ κ : ℕ) : ℤ) ≤ lim.word →
    Ends lim P d (powStmt κ) ⟨frame [a, n, 1], μ⟩ (4 * κ) (· = ⟨frame [a, n, ((n ^ κ : ℕ) : ℤ)], μ⟩)
  | 0, _ => Ends.skip (by simp)
  | κ + 1, hw => by
    have hle : ((n ^ κ : ℕ) : ℤ) ≤ ((n ^ (κ + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hn (by omega)
    have hval : ((n ^ κ : ℕ) : ℤ) * n = ((n ^ (κ + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    unfold powStmt
    refine Ends.next (4 * κ) ((pow_spec hn a μ κ (hle.trans hw)).mono le_rfl ?_)
    rintro _ rfl
    -- U := U * n
    refine Ends.setTo ((n ^ (κ + 1) : ℕ) : ℤ) rfl ⟨?_, ?_⟩
    · simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
         Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
         reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
         Nat.cast_zero, Nat.cast_one, ]
      change |((n ^ κ : ℕ) : ℤ) * n| ≤ lim.word
      rw [hval, abs_of_nonneg (Int.natCast_nonneg _)]
      exact hw
    · exact hval

























/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : EndStatement.Problem} (x : Bounded Q)

/-- Cell 0 holds the size. -/
theorem ofEnd_cell0 (loc : ℕ → ℤ) : (M (k 0)).val ⟨loc, memOf ((ofEnd Q).input x)⟩ = x.n := by
  simp [memOf]

/-- All cells of the input are within the size and the bound. -/
theorem ofEnd_input_le : ∀ a ∈ (ofEnd Q).input x, |a| ≤ ((x.n + x.U + 1 : ℕ) : ℤ) := by
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · rw [abs_of_nonneg (by positivity)]
    push_cast
    omega
  · have := Bounded.abs_le ha
    push_cast
    omega

/-- Cell 0 may be read. -/
theorem safe_cell0 {lim : Limits} {σ : State} (h0 : 0 ≤ lim.word) (h1 : 1 ≤ lim.space) :
    (M (k 0)).Safe lim σ := by
  simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
    Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
    reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, ]
  exact ⟨h0, le_rfl, by omega⟩

end OfEnd

/-! ## Polynomials in the size -/

/-- A polynomial in `n` and `U = n^κ` is a polynomial in `n`. -/
private theorem polyBound_pow_le (s k κ n : ℕ) {r : ℕ} (hr : (κ + 1) * k ≤ r) :
    polyBound s k [n, n ^ κ] ≤ 2 ^ (s + k) * (n + 1) ^ r := by
  have hpos : 1 ≤ n + 1 := by omega
  have hU : n ^ κ + 1 ≤ 2 * (n + 1) ^ κ := by
    have h1 : n ^ κ ≤ (n + 1) ^ κ := Nat.pow_le_pow_left (by omega) κ
    have h2 : 1 ≤ (n + 1) ^ κ := Nat.one_le_pow _ _ hpos
    omega
  unfold polyBound
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc 2 ^ s * ((n + 1) * (n ^ κ + 1)) ^ k
      ≤ 2 ^ s * ((n + 1) * (2 * (n + 1) ^ κ)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hU) k)
    _ = 2 ^ (s + k) * (n + 1) ^ ((κ + 1) * k) := by
        rw [show (n + 1) * (2 * (n + 1) ^ κ) = 2 * (n + 1) ^ (κ + 1) by ring, mul_pow, ← pow_mul,
          pow_add]
        ring
    _ ≤ 2 ^ (s + k) * (n + 1) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos hr)




































namespace Wrap

variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}


























/-- The limits of the run leave that room. -/
theorem room (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) :
    w.Room need x (w.limits need x) := by
  have hfr := w.fr_pos x
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp only [limits] <;> omega





/-- The run of the outermost procedure on an instance of size at least 1. -/
theorem body_ends (w : Wrap Q task dec) {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hsol : _root_.Light.Solves task P p Tn need) (κ : ℕ) (x : Bounded Q) (hn : 1 ≤ x.n) (hU : x.U = x.n ^ κ)
    {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ (Tn x.n x.U + w.bodySteps κ) (Answered x dec) := by
  have hbound := hroom.bound
  have hcells := hroom.cells
  have hdepth := hroom.depth
  have hcst : x.n * x.n + 1 ≤ w.cst * (x.n * x.n + 1) := Nat.le_mul_of_pos_left _ w.cst_pos
  have hsquare : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := le_trans (Nat.cast_le.2 (by omega)) hcells
  have hU1 : 1 ≤ x.U := hU ▸ Nat.one_le_pow _ _ hn
  push_cast at hbound hsquare
  unfold topBody bodySteps
  -- n := mem[0]
  refine Ends.setToThen (x.n : ℤ) ?_ ⟨safe_cell0 (by omega) hroom.space, ofEnd_cell0 x _⟩
  -- if n ≠ 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) (fun _ => ?_)
  -- U := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          1
            -- U := U * n, κ times
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- U := U * n, κ times
  refine Ends.next (4 * κ) ((pow_spec hn 0 _ κ (by rw [← hU]; omega)).mono le_rfl ?_)
  rintro _ rfl
  rw [← hU]
  -- local 3 := n * n
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (x.n * x.n : ℕ)
            -- result := solver(…)
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- result := solver(…)
  refine Ends.callToThen (hsol.meets _ (w.inst x) (w.fr x) (w.pre x hn hU1)
    (by rw [w.size_eq, w.bound_eq]; exact hroom.solver)) ?_
    ⟨w.safe x lim _ rfl rfl rfl hcells, w.vals x _ rfl rfl rfl⟩ (by omega)
    (by rw [w.size_eq, w.bound_eq]; first
                                    |
                                      ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                        (first
                                          | omega
                                          | ((ring_nf); (omega))))
                                    | omega
                                    |
                                      (simp [] <;>
                                          first
                                          | omega
                                          | ((ring_nf); (omega))))
  intro r μ' hpost
  rw [w.size_eq, w.bound_eq]
  have hanswer := w.post x r μ' hn hpost
  -- for a problem with an output: result := 1
  cases dec
  · exact Ends.set (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                          Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                          reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                          Nat.cast_zero, Nat.cast_one, ]; omega) (by first
                                                                     |
                                                                       ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                             List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                         (first
                                                                           | omega
                                                                           | ((ring_nf); (omega))))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | ((ring_nf); (omega)))) (by simpa [Answered] using hanswer)
  · exact Ends.skip (by simpa [Answered] using hanswer)

/-- The run of the outermost procedure on an instance of size 0. -/
theorem body_ends_zero (w : Wrap Q task dec) (P : Program) (p κ : ℕ) (x : Bounded Q) (hn : x.n = 0)
    {need : ℕ → ℕ → Need} {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ 9 (Answered x dec) := by
  have hbound := hroom.bound
  push_cast at hbound
  unfold topBody
  -- n := mem[0]
  refine Ends.setToThen (x.n : ℤ) ?_ ⟨safe_cell0 (by omega) hroom.space, ofEnd_cell0 x _⟩
  -- if n ≠ 0 … else result := 0 or 1
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [hn]) h)
  have hanswer := w.zero x hn
  cases dec <;>
    exact Ends.set (by simp; omega) (by first
                                        |
                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                            (first
                                              | omega
                                              | ((ring_nf); (omega))))
                                        | omega
                                        |
                                          (simp [] <;>
                                              first
                                              | omega
                                              | ((ring_nf); (omega)))) (by simpa [Answered, verdictOf] using hanswer _)

/-- The outermost call, from the run of its procedure. -/
theorem ends_of_body (w : Wrap Q task dec) {P : Program} {p κ T : ℕ} (x : Bounded Q)
    {need : ℕ → ℕ → Need}
    (h : Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ T (Answered x dec)) :
    Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 0 (mainStmt P.length)
      ⟨frame [0, 0, 0], memOf ((ofEnd Q).input x)⟩ (T + 4) (Answered x dec) :=
  Ends.call T (by simp) (by simp) (by simp only [limits]; omega)
    (h.mono le_rfl fun _ hσ => by simpa [Answered] using hσ) (by first
                                                                   |
                                                                     ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                           List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                       (first
                                                                         | omega
                                                                         | ((ring_nf); (omega))))
                                                                   | omega
                                                                   |
                                                                     (simp [] <;>
                                                                         first
                                                                         | omega
                                                                         | ((ring_nf); (omega))))

/-- The limits are polynomial in the size. -/
theorem small (w : Wrap Q task dec) {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (κ : ℕ) :
    ∃ s k : ℕ, ∀ x : Bounded Q, x.U = x.n ^ κ → Small s k [x.n] (w.limits need x) := by
  obtain ⟨s, k, hpoly⟩ := hpoly
  obtain ⟨r, hr⟩ : ∃ r, r = (κ + 1) * k + κ + 2 := ⟨_, rfl⟩
  refine ⟨s + k + 5 + Nat.size w.cst, r, fun x hU => ?_⟩
  obtain ⟨hword, hcells, hdepth⟩ := hpoly x.n x.U
  have hpos : 1 ≤ x.n + 1 := by omega
  have hneed := polyBound_pow_le s k κ x.n (r := r) (by omega)
  have hsquare : x.n * x.n + 1 ≤ (x.n + 1) ^ r :=
    (by nlinarith : x.n * x.n + 1 ≤ (x.n + 1) ^ 2).trans (Nat.pow_le_pow_right hpos (by omega))
  have hbound : x.n ^ κ ≤ (x.n + 1) ^ r :=
    (Nat.pow_le_pow_left (by omega) κ).trans (Nat.pow_le_pow_right hpos (by omega))
  have hsize : x.n + 1 ≤ (x.n + 1) ^ r := Nat.le_self_pow (by omega) _
  have hfr := w.fr_le x
  rw [← hU] at hneed hbound
  -- `X` bounds the parts that do not come from the solver, `Z ≥ X` those that do
  have hXZ : (x.n + 1) ^ r ≤ 2 ^ (s + k) * (x.n + 1) ^ r := Nat.le_mul_of_pos_left _ (by positivity)
  have hgoal : polyBound (s + k + 5 + Nat.size w.cst) r [x.n] =
      32 * (2 ^ Nat.size w.cst * (2 ^ (s + k) * (x.n + 1) ^ r)) := by
    unfold polyBound
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_add 2 (s + k + 5) (Nat.size w.cst), pow_add 2 (s + k) 5]
    ring
  generalize 2 ^ (s + k) * (x.n + 1) ^ r = Z at *
  generalize (x.n + 1) ^ r = X at *
  -- `Y ≥ Z` takes in the constant of the layout
  have hcst : w.cst * (x.n * x.n + 1) ≤ 2 ^ Nat.size w.cst * Z :=
    Nat.mul_le_mul (Nat.lt_size_self w.cst).le (hsquare.trans hXZ)
  have hZY : Z ≤ 2 ^ Nat.size w.cst * Z := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  generalize 2 ^ Nat.size w.cst * Z = Y at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [limits, hgoal] <;> omega

/-- The compiled program is run within these limits: what the interface to the machine asks for. -/
theorem topSolves (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (hsol : _root_.Light.Solves task P p Tn need)
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u) (κ : ℕ) :
    ∃ s k : ℕ, ProgramSolves (ofEnd Q) (P ++ [topBody κ p w.args dec]) P.length dec s k
      (fun x => x.U = x.n ^ κ) fun x => max (T x.n x.U) 0 + w.extra κ := by
  obtain ⟨s, k, hsmall⟩ := w.small hpoly κ
  refine ⟨s, k, fun x hU => ?_⟩
  have hinput : ∀ a ∈ (ofEnd Q).input x, |a| ≤ (w.limits need x).word := fun a ha =>
    (ofEnd_input_le x a ha).trans (by simp only [limits]; omega)
  rcases Nat.eq_zero_or_pos x.n with hn | hn
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends_zero P p κ x hn (w.room need x))
    have hc' : (c : ℝ) ≤ w.extra κ := by exact_mod_cast hc.trans (by unfold extra bodySteps; omega)
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_right (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends hsol κ x hn hU (w.room need x))
    have hc' : (c : ℝ) ≤ (Tn x.n x.U : ℝ) + w.extra κ := by
      exact_mod_cast hc.trans (by unfold extra; omega)
    have hTn := hT x.n x.U x.U hn (hU ▸ Nat.one_le_pow _ _ hn) le_rfl
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_left (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩

/-- **If the task is solved in time T, the problem is solved on the word RAM within a constant times
T.** -/
theorem realized_sourceProof (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) : Realized Q T := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  intro κ
  obtain ⟨s, k, htop⟩ := w.topSolves hpoly hsol hT κ
  refine ⟨_, _, (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) * (w.extra κ + 1),
    by positivity,
    (solves_of_programSolves htop (r := 1) fun x => by simp).mono le_rfl (fun _ hx => hx)
      fun x _ => ?_⟩
  -- `K (T + E) + K ≤ K (E + 1) T + K (E + 1)` for `K, E, T ≥ 0`
  have hT0 : (0 : ℝ) ≤ max (T x.n x.U) 0 := le_max_right _ _
  have hK : (0 : ℝ) ≤ (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) := by positivity
  have hE : (0 : ℝ) ≤ (w.extra κ : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hK hE) hT0]

end Wrap

end Light

end
end


theorem solution : ∀ {Q : EndStatement.Problem} {task : Light.Task} {dec : Bool} (w : Light.Wrap Q task dec) {T : Nat → Real → Real},
  Light.SolvedIn task T → ThreeSumApsp.WordRam.Realized Q T := by
  exact @Light.Wrap.realized_sourceProof

#print axioms solution
