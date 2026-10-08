-- Prove2me | solution 1 for Light.Sec4.queryAt_spec
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:28:44.694732+00:00
-- url     : https://prove2.me/submissions/89629f1b-0bd4-4ea8-920b-fe986f067ec6

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma6
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma7_8
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Levels
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Boxes
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_BoxesFromLeaves
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Lemma27_28
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Theorem30
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Cubes
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Trie
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSumApsp_Mult_arrays_eq_mul
import Theorems.Thm_ThreeSumApsp_Spec_TrieRep_insert
import Theorems.Thm_ThreeSumApsp_Spec_abs_dpValue_le
import Theorems.Thm_ThreeSumApsp_Spec_length_nineStrs
import Theorems.Thm_ThreeSumApsp_Spec_mem_nineStrs
import Theorems.Thm_ThreeSumApsp_Spec_pairwise_lt_nineStrs
import Theorems.Thm_ThreeSumApsp_eq_lowest_of_lt
import Theorems.Thm_ThreeSumApsp_getD_weaveList
import Theorems.Thm_ThreeSumApsp_lemma_29_split
import Theorems.Thm_ThreeSumApsp_sec2_card_contributing_of_order

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

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












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

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

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
  Ends.next T₁ (h.mono le_rfl rest) hT

/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by first
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
    Ends lim P d s σ T Q :=
  h.mono hT rest































































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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}













/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)






/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/









































end Light

end
end

section


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/





/-- Row `a < m` ends within the matrix: `a * n + b ≤ m * n` for `b ≤ n`, so also for `b = n`. -/
theorem mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := Nat.add_le_add_left hb _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha

/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

































/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

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

/-- Entry `j` of the second of two lists put together. -/
theorem getD_append_add (l l' : List α) (j : ℕ) (d : α) :
    (l ++ l').getD (l.length + j) d = l'.getD j d := by
  rw [List.getD_append_right l l' d _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

































/-- One more member at the end changes the entry number `l.length` only. -/
theorem getD_append_singleton (l : List α) (a d : α) :
    (fun e => (l ++ [a]).getD e d) = Function.update (fun e => l.getD e d) l.length a := by
  funext e
  rcases Nat.lt_trichotomy e l.length with he | rfl | he
  · rw [Function.update_of_ne he.ne, List.getD_append _ _ _ _ he]
  · rw [Function.update_self, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
      List.getD_cons_zero]
  · rw [Function.update_of_ne he.ne', List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ he.le]







/-! ## Blocks one after the other -/

/-- Blocks of any lengths: entry `o` of block `r` stands after the blocks `0, …, r - 1`. -/
theorem getD_flatMap_range_sum (f : ℕ → List α) {n r o : ℕ} (hr : r < n) (ho : o < (f r).length)
    (d : α) :
    ((List.range n).flatMap f).getD (((List.range r).map fun s => (f s).length).sum + o) d =
      (f r).getD o d := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [Nat.add_assoc, List.range_add, List.flatMap_append, ← List.length_flatMap, getD_append_add,
    Nat.add_comm c 1, List.range_add, List.map_append, List.flatMap_append,
    List.getD_append _ _ _ _ (by simpa using ho)]
  simp

/-- The length of `n` blocks of length `k`. -/
theorem length_flatMap_range {k : ℕ} (n : ℕ) (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) :
    ((List.range n).flatMap f).length = n * k := by
  rw [List.length_flatMap,
    List.map_congr_left (g := fun _ => k) fun z hz => hf z (List.mem_range.1 hz)]
  simp

/-- Blocks of length `k`: entry `r` of block `z` has the index `z * k + r`. -/
theorem getD_flatMap_range {k n : ℕ} (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) {z r : ℕ}
    (hz : z < n) (hr : r < k) (d : α) :
    ((List.range n).flatMap f).getD (z * k + r) d = (f z).getD r d := by
  rw [← length_flatMap_range z f fun s hs => hf s (hs.trans hz), List.length_flatMap]
  exact getD_flatMap_range_sum f hz (hf z hz ▸ hr) d


















































/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl



































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- The triangle inequality for the sum of a list. -/
theorem abs_sum_le_sum_abs (l : List R) : |l.sum| ≤ (l.map fun x => |x|).sum :=
  Multiset.abs_sum_le_sum_abs (s := (l : Multiset R))

/-- The sum of an initial part of a list is at most the sum of the absolute values of the whole
list, in absolute value. -/
theorem abs_sum_take_le_sum_abs (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by
  refine (abs_sum_le_sum_abs _).trans ?_
  refine Sublist.sum_le_sum ((take_sublist k l).map _) fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := mem_map.mp ha
  exact abs_nonneg x

end














/-- If `l` has no repetitions, every member of `l` is `g x` for some `x ∈ S`, `g` is injective and
`l` has as many members as `S` has elements, then the members of `l` are exactly the `g x` with
`x ∈ S`. -/
theorem toFinset_eq_image_of_length_eq_card [DecidableEq β] (l : List β) (hl : l.Nodup)
    (S : Finset α) (g : α → β)
    (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y) (hcard : l.length = S.card) :
    l.toFinset = S.image g := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := hsub y (List.mem_toFinset.mp hy)
    exact Finset.mem_image_of_mem g hx
  · rw [Finset.card_image_of_injective S hinj, List.toFinset_card_of_nodup hl, hcard]

/-- Under the same hypotheses, a sum over `l` is a sum over `S`. -/
theorem sum_map_eq_sum_of_length_eq_card {M : Type*} [AddCommMonoid M] (l : List β) (hl : l.Nodup)
    (S : Finset α)
    (g : α → β) (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y)
    (hcard : l.length = S.card) (F : β → M) : (l.map F).sum = ∑ x ∈ S, F (g x) := by
  classical
  rw [← List.sum_toFinset F hl, toFinset_eq_image_of_length_eq_card l hl S g hinj hsub hcard,
    Finset.sum_image fun x _ y _ hxy => hinj hxy]

/-! ## A running minimum -/
























/-! ## Counting -/

























































/-- How often a value occurs among the first `i` values of a function on `Fin n`. -/
theorem count_take_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) (i : ℕ) :
    ((List.ofFn f).take i).count a =
      (Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ f j = a).card := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.ofFn_succ, List.take_succ_cons, List.count_cons, ih, Finset.card_filter,
        Finset.card_filter, Fin.sum_univ_succ, add_comm]
      simp

/-- How often a value occurs in the table of a function on `Fin n`. -/
theorem count_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = (Finset.univ.filter fun i => f i = a).card := by
  simpa [List.take_of_length_le] using count_take_ofFn f a n

/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/



















/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]































/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)






















/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]




































































end Light

end
end

section


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]





namespace PowTable









end PowTable

open PowTable




































































end Light

end
end

section


/-!
# Strings cut along a set of levels

Section 2.3.3 cuts a string of `L` variables along a set `Q` of `m` levels: its variables
at the levels of `Q`, in the order of the levels, form a string of length `m`, and its variables at
the other levels form a string of length `L - m`. The first three parts of this file hold for every
alphabet; the last part specializes them to left, right and output strings.

* Every level is the `k`-th lowest level of `Q` or the `k`-th lowest level outside `Q` for some `k`.
  So a statement about all levels is checked on these two kinds of levels (`forall_level_iff`), and
  so is the statement that a set of levels is `Q` (`filter_eq_iff_forall_level`).
* `glue Q hQ f g` is the string with the letters of `f` at the levels of `Q` and the letters of `g`
  at the other levels. It is the only such string (`eq_glue_iff`), and `f` and `g` can be read off
  it (`glue_inj`).
* If the letters are of two kinds, inner and outer, and each is given by its kind and an index, then
  a string can be rebuilt from its inner set and the indices of its letters (`glue_index`).
* "A string is determined by its inner set, its outer part, and its inner part": the strings
  `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and `outStrOf Q hQ r c` have the parts that their
  names say, and no other string has them (`existsUnique_leftStr`, `existsUnique_rightStr`,
  `existsUnique_outStr`). No later proof uses these three statements; the later proofs use the
  lemmas from which they follow.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### The levels of a set and of its complement, in order -/

/-- The `k`-th lowest level of `Q` is a level of `Q`. -/
theorem innerLevel_mem (k : Fin m) : innerLevel Q hQ k ∈ Q :=
  Q.orderEmbOfFin_mem hQ k

/-- The `k`-th lowest level outside `Q` is not a level of `Q`. -/
theorem outerLevel_notMem (k : Fin (L - m)) : outerLevel Q hQ k ∉ Q :=
  mem_compl.mp (Qᶜ.orderEmbOfFin_mem (card_compl_of_card_eq Q hQ) k)

/-- Every level of `Q` is the `k`-th lowest level of `Q` for some `k`. -/
theorem exists_innerLevel {ℓ : Fin L} (hℓ : ℓ ∈ Q) : ∃ k, innerLevel Q hQ k = ℓ :=
  (Q.range_orderEmbOfFin hQ).ge hℓ

/-- Every level outside `Q` is the `k`-th lowest level outside `Q` for some `k`. -/
theorem exists_outerLevel {ℓ : Fin L} (hℓ : ℓ ∉ Q) : ∃ k, outerLevel Q hQ k = ℓ :=
  (Qᶜ.range_orderEmbOfFin (card_compl_of_card_eq Q hQ)).ge (mem_coe.mpr (mem_compl.mpr hℓ))













/-- A property holds at every level if and only if it holds at the levels of `Q` and at the levels
outside `Q`. -/
theorem forall_level_iff {P : Fin L → Prop} :
    (∀ ℓ, P ℓ) ↔ (∀ k, P (innerLevel Q hQ k)) ∧ ∀ k, P (outerLevel Q hQ k) := by
  refine ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hin, hout⟩ ℓ => ?_⟩
  by_cases hℓ : ℓ ∈ Q
  · obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
    exact hin k
  · obtain ⟨k, rfl⟩ := exists_outerLevel Q hQ hℓ
    exact hout k

/-- A property cuts out the set `Q` if and only if it holds at the levels of `Q` and fails at the
other levels. -/
theorem filter_eq_iff_forall_level {P : Fin L → Prop} [DecidablePred P] :
    univ.filter P = Q ↔ (∀ k, P (innerLevel Q hQ k)) ∧ ∀ k, ¬ P (outerLevel Q hQ k) := by
  simp only [Finset.ext_iff, forall_level_iff Q hQ, mem_filter, mem_univ, true_and,
    innerLevel_mem, outerLevel_notMem, iff_true, iff_false]








/-! ### Gluing two strings along a set of levels -/

variable {α : Type*}








/-- At the `k`-th lowest level of `Q`, the glued string has the `k`-th letter of `f`. -/
@[simp]
theorem glue_innerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin m) :
    glue Q hQ f g (innerLevel Q hQ k) = f k := by
  rw [glue, dif_pos (innerLevel_mem Q hQ k)]
  exact congrArg f ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level outside `Q`, the glued string has the `k`-th letter of `g`. -/
@[simp]
theorem glue_outerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin (L - m)) :
    glue Q hQ f g (outerLevel Q hQ k) = g k := by
  rw [glue, dif_neg (outerLevel_notMem Q hQ k)]
  exact congrArg g ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))














variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}

/-- The glued string is the only string with the letters of `f` at the levels of `Q` and the letters
of `g` at the other levels. -/
theorem eq_glue_iff {u : Fin L → α} :
    u = glue Q hQ f g
      ↔ (∀ k, u (innerLevel Q hQ k) = f k) ∧ ∀ k, u (outerLevel Q hQ k) = g k := by
  simp only [funext_iff, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel]






/-- A map applied to a glued string, letter by letter. -/
theorem map_glue {β : Type*} (φ : α → β) :
    (fun ℓ => φ (glue Q hQ f g ℓ)) = glue Q hQ (fun k => φ (f k)) (fun k => φ (g k)) := by
  simp only [eq_glue_iff, glue_innerLevel, glue_outerLevel, implies_true, and_self]

/-! ### Alphabets with inner and outer letters -/

variable (IsInner : α → Prop) [DecidablePred IsInner]

/-- If the letters of `f` are inner and those of `g` are outer, then the glued string has its inner
letters exactly at the levels of `Q`. -/
theorem filter_glue (hf : ∀ k, IsInner (f k)) (hg : ∀ k, ¬ IsInner (g k)) :
    (univ.filter fun ℓ => IsInner (glue Q hQ f g ℓ)) = Q := by
  simpa only [filter_eq_iff_forall_level Q hQ, glue_innerLevel, glue_outerLevel] using
    And.intro hf hg













/-! ### Left, right and output strings with a given inner set, outer part and inner part -/



























/-- The inner set of `outStrOf Q hQ r c` is `Q`. -/
@[simp]
theorem innerSetO_outStrOf (r c : OuterStr L m) : innerSetO (outStrOf Q hQ r c) = Q :=
  filter_glue Q hQ OutVar.IsInner (fun _ => trivial) fun _ => id















































variable {Q}



































variable {hQ}

















variable (Q) (hQ)
include hQ




































end ThreeSumApsp

end
end

section


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/











namespace Par






















/-! ## The shared block, from its base address `b0` on -/











































end Par








/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)





























end Par











end Light.Sec2

end
end

section


/-!
# Lemma 6: Schönhage's identity

Sections 2.1 and 2.2. After Strassen's identity (equation (1)), which the paper
recalls, this file treats Schönhage's. It has ten terms `λ`, each the product of a linear form `φ_λ`
in the seven left variables, a linear form `ψ_λ` in the seven right variables and a linear form
`χ_λ` in the ten output variables. Lemma 6 says that `∑_λ φ_λ ψ_λ χ_λ = G + E`, an identity of
polynomials in the 24 variables: `G` holds the outer product and the inner product that are wanted,
and `E` is an error.

* A linear form is the vector of its coefficients. `formL`, `formR` and `formO` turn it into a
  polynomial, and they are linear (`formL_eq_linearCombination` and its two companions).
* The proof of `lemma_6` is the paper's. The coefficient of `z_ij` comes only from the term `P_ij`.
  In the coefficient of `z₀` the products `x_i y_j` cancel, the cross terms vanish because the
  columns of `p̂` and the rows of `q̂` sum to zero (`pHat_column_sum`, `qHat_row_sum`), and what
  remains is the inner product (`sum_pHat_mul_qHat`).
* Second observation after the lemma: every term contributes to `z₀`, and only `P_ij` contributes to
  `z_ij` (`Term.contributes_z0`, `Term.contributes_z_iff`).

The later files on Section 2 use the second observation and the coefficients of the forms; none of
their proofs uses `lemma_6`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp















/-! ### The alphabets -/


































/-- Section 2.2: there are "seven left variables". -/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- Section 2.2: there are "seven right variables". -/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]

/-- Section 2.2: "Schönhage's identity has ten terms". -/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]







/-! ### Linear forms as polynomials -/























































/-! ### Lemma 6 -/



































/-! ### Which terms contribute to which output variables -/

/-- Section 2.2, second observation: "every term contributes to z₀". -/
@[simp]
theorem Term.contributes_z0 (lam : Term) : lam.Contributes .z0 := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form]

/-- Section 2.2, second observation: "only P_ij contributes to z_ij". -/
@[simp]
theorem Term.contributes_z_iff (lam : Term) (i j : Fin 3) :
    lam.Contributes (.z i j) ↔ lam = .P i j := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form, Pi.single_apply, eq_comm]

/-- The second observation in one statement: a term contributes to `z` if and only if `z` is inner,
that is `z₀`, or the term is `z.privateTerm`, which is `P_ij` for `z = z_ij`. (This is the term that
the private leaf of Section 2.4.3 has at a level with the variable `z`.) -/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert

/-- A sum over the terms contributing to `z` has the one summand `P_ij` for `z = z_ij`, and runs
over all terms for `z = z₀`. This is how step (4) of the recursions assembles the slice at `z`. -/
theorem Term.sum_contributes {A : Type*} [AddCommMonoid A] (c : Term → A) (z : OutVar) :
    ∑ lam : Term with lam.Contributes z, c lam
      = match z with
        | .z i j => c (.P i j)
        | .z0 => ∑ lam, c lam := by
  cases z with
  | z i j => simp [filter_eq']
  | z0 => simp







end ThreeSumApsp

end
end

section


/-!
# Lemmas 7 and 8: what `Full` computes

Section 2.3.2. Lemma 7: at the leaf `τ`, `Full(a, b)` multiplies `Φ_τ(a)` by
`Ψ_τ(b)`, and it returns `Mult(a, b)`, whose entry at `w` is the sum of these products over the
leaves contributing to `w` (equation (2)). Lemma 8:
`Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) ⋯ γ(u_L, v_L, w_L) a[u] b[v]`, with the `γ` of equation (3).

* `Φ_τ` and `Ψ_τ` are the same expression for two families of linear forms (`encodeWith`), so what
  holds for both is proved once.
* Lemma 7 is proved by induction on `L`, as in the paper. Step (2) is the encoding:
  `Φ_{λτ'}(a) = Φ_{τ'}(A_λ)` and `Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)` (`Phi_cons`, `Psi_cons`). Step (4) is
  the decoding: the leaves contributing to `z w'` are the `λτ'` with `λ` contributing to `z` and
  `τ'` to `w'` (`Leaf.contributes_succ`), so `Full` and `Mult` both satisfy
  `c[z w'] = ∑_{λ contributing to z} C_λ[w']` (`Full_succ`, `Mult_succ`).
* Lemma 8: the leaves contributing to `w` choose a term contributing to `w_ℓ` independently at each
  level `ℓ` (`Leaf.filter_contributes_eq_piFinset`), so the sum over these leaves of a product over
  the levels is a product of sums (`prod_gamma_eq_sum_contributes`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Which leaves contribute to an output string -/

/-- In the proof of Lemma 7: "the leaves contributing to zw' are the λτ' with λ
contributing to z and τ' contributing to w'".  Here `λ = τ 0`, `τ' = Fin.tail τ`, `z = w 0` and
`w' = Fin.tail w`. -/
theorem Leaf.contributes_succ {L : ℕ} {τ : Leaf (L + 1)} {w : OutStr (L + 1)} :
    Leaf.Contributes τ w
      ↔ (τ 0).Contributes (w 0) ∧ Leaf.Contributes (Fin.tail τ) (Fin.tail w) := by
  simp only [Leaf.Contributes, Fin.forall_fin_succ, Fin.tail]

/-- A sum over the strings of length `L + 1` is a sum over the first variable `s` and the rest `u'`
of the string `s u'`. -/
private theorem sum_strings_succ {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℤ) :
    ∑ u, f u = ∑ s, ∑ u', f (Fin.cons s u') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun _ => rfl).symm

/-- A sum over the leaves contributing to `w`, split by the first term of the leaf. -/
theorem Leaf.sum_contributes_succ {L : ℕ} (w : OutStr (L + 1)) (f : Leaf (L + 1) → ℤ) :
    ∑ τ : Leaf (L + 1) with Leaf.Contributes τ w, f τ
      = ∑ lam : Term with lam.Contributes (w 0),
          ∑ τ' : Leaf L with Leaf.Contributes τ' (Fin.tail w), f (Fin.cons lam τ') := by
  simp only [sum_filter, sum_strings_succ, Leaf.contributes_succ, Fin.cons_zero,
    Fin.tail_cons]
  refine sum_congr rfl fun lam _ => ?_
  by_cases h : lam.Contributes (w 0) <;> simp [h]

/-- In the proof of Lemma 8: the leaves contributing to `w` "are the leaves whose term at
level ℓ contributes to w_ℓ, independently for each ℓ". -/
theorem Leaf.filter_contributes_eq_piFinset {L : ℕ} (w : OutStr L) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w)
      = Fintype.piFinset fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ) := by
  ext τ
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rfl







/-! ### The two encodings at once -/

section encodeWith

variable {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}






/-- For `L = 0` the only string is empty, and so are the products over the levels. -/
theorem encodeWith_zero (τ : Leaf 0) (a : (Fin 0 → α) → ℤ) : encodeWith c τ a = a Fin.elim0 := by
  simp [encodeWith, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]

/-- The number at the leaf `λτ'` for `a` is the number at the leaf `τ'` for `∑_s c_λ(s) a_s`. -/
theorem encodeWith_cons (lam : Term) (τ' : Leaf L) (a : (Fin (L + 1) → α) → ℤ) :
    encodeWith c (Fin.cons lam τ' : Leaf (L + 1)) a
      = encodeWith c τ' fun u' => ∑ s, c lam s * sliceAt a s u' := by
  simp only [encodeWith, sum_strings_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sliceAt, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun u' _ => sum_congr rfl fun s _ => by ring

end encodeWith

/-! ### Lemma 7 -/

/-- In the proof of Lemma 7: "for every leaf λτ' we have
Φ_{λτ'}(a) = ∑_s φ_λ(s) Φ_{τ'}(a_s) = Φ_{τ'}(A_λ)". -/
theorem Phi_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (a : LeftStr (L + 1) → ℤ) :
    Phi (Fin.cons lam τ' : Leaf (L + 1)) a = Phi τ' (encodeStepL lam a) :=
  encodeWith_cons phi lam τ' a

/-- In the proof of Lemma 7: "and similarly Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)". -/
theorem Psi_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (b : RightStr (L + 1) → ℤ) :
    Psi (Fin.cons lam τ' : Leaf (L + 1)) b = Psi τ' (encodeStepR lam b) :=
  encodeWith_cons psi lam τ' b

/-- "For L = 0, the only leaf is the empty string τ, and Φ_τ(a) = a […], as the products over the
levels are empty" (proof of Lemma 7). -/
private theorem Phi_zero (τ : Leaf 0) (a : LeftStr 0 → ℤ) : Phi τ a = a Fin.elim0 :=
  encodeWith_zero phi τ a

/-- "and Ψ_τ(b) = b" (proof of Lemma 7). -/
private theorem Psi_zero (τ : Leaf 0) (b : RightStr 0 → ℤ) : Psi τ b = b Fin.elim0 :=
  encodeWith_zero psi τ b















/-- Step (4) of `Full`, as it is read in the proof of Lemma 7:
`c[z w'] = ∑_{λ contributing to z} C_λ[w']`. -/
theorem Full_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Full (L + 1) a b w = ∑ lam : Term with lam.Contributes (w 0),
      Full L (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  rw [Term.sum_contributes]
  rfl

/-- In the proof of Lemma 7:
`Mult(a, b)[z w'] = ∑_{λ contributing to z} Mult(A_λ, B_λ)[w']`. -/
theorem Mult_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Mult a b w = ∑ lam : Term with lam.Contributes (w 0),
      Mult (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  simp only [Mult, Leaf.sum_contributes_succ, Phi_cons, Psi_cons]

/-- **Lemma 7**, second half.  "and it returns Mult(a, b)." -/
theorem Lemma7.returns_Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    Full L a b = Mult a b := by
  induction L with
  | zero =>
    funext w
    simp [Full, Full.run, Mult, Leaf.Contributes, Phi_zero, Psi_zero]
  | succ L ih =>
    funext w
    simp only [Full_succ, Mult_succ, ih]







/-! ### Lemma 8 -/


























end ThreeSumApsp

end
end

section


/-!
# Lemma 9: one run of `Full` computes all the products `X_Q Y_Q`

Section 2.3.3. The inner set of a string is the set of the levels at which it has
an inner variable (`p`, `q` or `z₀`). For a set `Q` of `m` levels, the left strings with inner set
`Q` index the entries of an `N₀ × D` matrix `X_Q`, the right strings those of a `D × N₀` matrix
`Y_Q`, and the output strings those of the product `X_Q Y_Q`. The arrays `a` and `b` hold all the
`X_Q` and all the `Y_Q` side by side. Lemma 9 says that `Mult(a, b)[w] = (X_Q Y_Q)[w]` for every
output string `w` with such an inner set.

* The strings with inner set `Q` are `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and
  `outStrOf Q hQ r c` (`existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`). At
  the first two the arrays hold `X_Q[r, π]` and `Y_Q[π, c]` (`arrayL_leftStrOf`,
  `arrayR_rightStrOf`).
* The two facts about `γ` that the proof needs are finite checks on the definition of `gamma`
  (`gamma_z0`, `gamma_x_y_z`); no other lemma is used for them.
* The proof of Lemma 9. By Lemma 8 the entry at `w` is a sum over all pairs `(u, v)`. In a summand
  that is not zero, `u` has inner set `Q`, the row of `w` as its outer part and some inner part `π`,
  and `v` has inner set `Q`, the column of `w` as its outer part and the same inner part
  (`exists_of_summand_ne_zero`). Each of these summands has coefficient 1 (`prod_gamma_eq_one`).
  Their sum is the entry of the matrix product (`Mult_arrays_eq_mul`, `lemma_9`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The sizes of the matrices, and Figure 4 -/
















































/-! ### The input arrays -/



















/-! ### The proof of Lemma 9 -/











































































































/-- Section 2.3.3: "one run of Full […] computes all K of the products X_Q Y_Q." -/
theorem Full_arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Full L (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  rw [Lemma7.returns_Mult]
  exact Mult_arrays_eq_mul X Y Q hQ r c

end ThreeSumApsp

end
end

section


/-!
# The tiling of the `N × D × N` product

Section 2.3.4. One run of `Full` computes `K` products of shape `N₀ × D × N₀` (Lemma 9).
To multiply an `N × D` matrix `X` by a `D × N` matrix `Y`, cut `X` into row blocks and `Y` into
column blocks of size `N₀`, group the blocks into bands of `K₀ = ⌊√K⌋` blocks, and call a row band
together with a column band a tile. Each tile is one run of `Full`, on a `K₀ × K₀` grid of block
products.

* The numbers: `K₀² ≤ K ≤ 4 K₀²` (`K0_sq_le_K`, `K_le_four_mul_K0_sq`), padding `N ≥ K₀ N₀` to
  a multiple of `K₀ N₀` at most doubles it (`le_padN`, `padN_lt_add_bandSize`, `padN_le_two_mul`),
  and there are at most `4N²/M` tiles, where `N` is the padded size (`card_tiles_mul_M_le`).
* A table of `K₀²` distinct subsets of size `m` exists (`nonempty_layout`; no later proof uses
  this).
* One run computes all the block products of a tile (`Full_bandArray_eq_block_mul`, from Lemma 9),
  and the entry `(XY)[I, J]` is the output of the run on the tile of `(I, J)` at the output string
  of `(I, J)` (`Full_bandArray_eq_mul`).
* Different positions of a tile have different output strings (`outStrOfPos_injective`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The numbers -/















/-- A band has at least one row. -/
theorem bandSize_pos {L m : ℕ} (hmL : m ≤ L) : 0 < bandSize L m :=
  Nat.mul_pos (K0_pos hmL) (N0_pos L m)





/-- The padded size is at least `N`.

NOTE. `m ≤ L` is left implicit in the paper. For `m > L` there is no subset of size `m` and
`K₀ = 0`. -/
theorem le_padN {L m : ℕ} (hmL : m ≤ L) (N : ℕ) : N ≤ padN L m N := by
  have h := Nat.lt_div_mul_add (a := N + bandSize L m - 1) (bandSize_pos hmL)
  unfold padN numBands
  omega




































/-! ### The table of subsets and the matrices of a tile -/


















/-- The subsets in the table are distinct, so a sum over the table that selects the subset of the
block product `gh` has one term. -/
private theorem sum_table_eq {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (∑ gh', if lay.table gh' = lay.table gh then F gh' else 0) = F gh := by
  simp [lay.table_injective.eq_iff]

/-- Section 2.3.4: "In a tile, let X_Q and Y_Q be the row block and the column block of the block
product with subset Q".  For `X_Q`: it is the `g`-th row block of the row band. -/
@[simp]
theorem bandFamilyL_table {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyL lay X β (lay.table (g, h)) = rowBlock lay X (β * K0 L m + g) :=
  sum_table_eq lay _ (g, h)

/-- The matrix `Y_Q` of the block product in position `(g, h)` is the `h`-th column block of the
column band. -/
@[simp]
theorem bandFamilyR_table {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyR lay Y β (lay.table (g, h)) = colBlock lay Y (β * K0 L m + h) :=
  sum_table_eq lay _ (g, h)











/-! ### One run of `Full` for each tile -/

/-- Section 2.3.4: "Then one run of Full computes all K₀² block products of the tile (Lemma 9)".
The tile is that of the row band `β` and the column band `β'`; the block product in position `(g,
h)` of its grid is the product of the row block `β K₀ + g` by the column block `β' K₀ + h`. -/
theorem Full_bandArray_eq_block_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β β' : ℕ)
    (g h : Fin (K0 L m)) (r c : OuterStr L m) :
    Full L (bandArrayL lay X β) (bandArrayR lay Y β')
        (outStrOf (lay.table (g, h)) (lay.table_card (g, h)) r c)
      = (rowBlock lay X (β * K0 L m + g) * colBlock lay Y (β' * K0 L m + h)) r c := by
  rw [bandArrayL, bandArrayR, Full_arrays_eq_mul, bandFamilyL_table, bandFamilyR_table]

/-- A row (or column) is recovered from its band, the position of its block in the band and its
position in the block. -/
private theorem position_decomp {L m : ℕ} (lay : Layout L m) (I : ℕ) :
    (bandOf L m I * K0 L m + (blockOf lay I : ℕ)) * N0 L m + (offsetOf L m I : ℕ) = I := by
  have hband : bandOf L m I = I / N0 L m / K0 L m := by
    rw [bandOf, bandSize, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have hblock : bandOf L m I * K0 L m + (blockOf lay I : ℕ) = I / N0 L m := by
    rw [hband]
    exact Nat.div_add_mod' _ _
  rw [hblock]
  exact Nat.div_add_mod' _ _

/-- Section 2.3.4: "and running it on every tile computes all of XY." The entry `(XY)[I, J]` is the
output of the run on the tile of `(I, J)` at the output string of `(I, J)`. -/
theorem Full_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Full L (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  unfold outStrOfPos
  rw [Full_bandArray_eq_block_mul, Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp lay.innerIdx]
  -- Both sides are sums over the `D` inner indices; the summands agree because row `I` is recovered
  -- from its band, block and place in the block, and likewise column `J`.
  refine sum_congr rfl fun k _ => ?_
  simp only [rowBlock, colBlock, Equiv.symm_apply_apply, position_decomp, padRows, padCols,
    I.isLt, J.isLt, dif_pos, Fin.eta]

/-- The entry `(XY)[I, J]` as a value of `Mult`, that is, as a sum over leaves (equation (2)). This
is the form in which Section 4 uses the tiling ("by (2) and Lemma 9, (X_Q Y_Q)[w] is the sum of the
products at the leaves contributing to w"). -/
theorem Mult_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Mult (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma7.returns_Mult]
  exact Full_bandArray_eq_mul lay X Y I J

/-- Every row and every column lies in one of the bands.

NOTE.  `m ≤ L` is left implicit in the paper. -/
theorem bandOf_lt_numBands {L m : ℕ} (hmL : m ≤ L) (N I : ℕ) (hI : I < N) :
    bandOf L m I < numBands L m N := by
  rw [bandOf, Nat.div_lt_iff_lt_mul (bandSize_pos hmL)]
  exact hI.trans_le (le_padN hmL N)

/-! ### The output string of a position -/

/-- Section 2.4.4: the inner set of the output string of a position is "the subset Q of the block
product containing (I, J)". -/
theorem innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    innerSetO (outStrOfPos lay I J) = lay.table (blockOf lay I, blockOf lay J) :=
  innerSetO_outStrOf _ _ _ _

/-- The inner set of the output string of a position has exactly `m` elements. -/
theorem card_innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    (innerSetO (outStrOfPos lay I J)).card = m :=
  innerSetO_outStrOfPos lay I J ▸ lay.table_card _
















end ThreeSumApsp

end
end

section


/-!
# Strings of digits as numbers

The paper indexes its arrays by strings (Section 2.3.1).  A program indexes them by numbers: the
string `d₁ d₂ ⋯ d_n` of digits in base `b` is coded by the number `d₁ b^{n-1} + ⋯ + d_n`.  The first
digit (the paper's level 1) is the most significant one, so the strings that begin with a given
digit have consecutive codes, and a slice of an array is a contiguous part of it.

* `code` is the number of a string, `digit` reads one digit of a number, `digitList` all of them,
  and `ofDigitList` is Horner's rule.
* `code` and `digit` undo each other (`digit_code`, `code_digit`), so the strings of length `n`
  correspond to the numbers below `b^n` (`codeEquiv`).
* For lists of digits, `digitList` undoes `ofDigitList` (`digitList_ofDigitList`). A list of `n`
  digits has a value below `b^n` (`ofDigitList_lt`), which determines it (`eq_of_ofDigitList_eq`).
  One more digit at the end is one more step of Horner's rule (`ofDigitList_append_singleton`,
  `ofDigitList_take_succ`).
* For an alphabet `α` whose letters are numbered by `e : α ≃ Fin b`, `codeStr e` and `decodeStr e`
  go from strings over `α` to numbers and back, so these strings, too, correspond to the numbers
  below `b^n` (`strEquiv`).  `digitsStr e` is the list of the digits of such a string; Horner's rule
  computes the code from it (`ofDigitList_digitsStr`).

Mathlib's `Nat.ofDigits` and `finFunctionFinEquiv` put the least significant digit first, so they
would make a slice a scattered part of an array; this is why the codes are defined here.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Strings of numbers below `b` -/





















/-- Horner's rule, started with `acc`, shifts `acc` by `n` digits and adds the code. -/
private theorem foldl_ofFn (b : ℕ) {n : ℕ} (d : Fin n → ℕ) (acc : ℕ) :
    (List.ofFn d).foldl (fun acc x => acc * b + x) acc = acc * b ^ n + code b d := by
  induction n generalizing acc with
  | zero => simp [code]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih, code, pow_succ, Fin.tail_def]
    ring

/-- The code is computed by Horner's rule, with one multiplication by `b` and one addition for each
digit. -/
theorem code_eq_ofDigitList (b : ℕ) {n : ℕ} (d : Fin n → ℕ) :
    code b d = ofDigitList b (List.ofFn d) := by
  rw [ofDigitList, foldl_ofFn, Nat.zero_mul, Nat.zero_add]




















































































/-! ## Lists of digits -/

/-- The list of the `n` digits of a number has `n` entries. -/
@[simp]
theorem length_digitList (b n c : ℕ) : (digitList b n c).length = n := by
  simp [digitList]

/-- Entry `i` of the list of digits is digit `i`. -/
@[simp]
theorem getElem_digitList (b n c : ℕ) {i : ℕ} (hi : i < (digitList b n c).length) :
    (digitList b n c)[i] = digit b n c i := by
  simp [digitList]

/-- The digits are below the base. -/
theorem lt_of_mem_digitList {b : ℕ} (hb : 0 < b) {n c x : ℕ} (hx : x ∈ digitList b n c) :
    x < b := by
  obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hx
  exact digit_lt hb n c ℓ

/-- The list of digits of a code. -/
theorem digitList_code {b n : ℕ} {d : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) :
    digitList b n (code b d) = List.ofFn d := by
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simpa using digit_code hd ⟨i, by simpa using hi⟩
















/-- The value of a list of digits is the code of the list, read as a string. -/
theorem ofDigitList_eq_code (b : ℕ) (l : List ℕ) :
    ofDigitList b l = code b fun ℓ : Fin l.length => l[(ℓ : ℕ)] := by
  rw [code_eq_ofDigitList, List.ofFn_getElem]







/-- The digits of the value of a list of digits below `b` are the list. -/
theorem digitList_ofDigitList {b : ℕ} (l : List ℕ) (hd : ∀ d ∈ l, d < b) :
    digitList b l.length (ofDigitList b l) = l := by
  rw [ofDigitList_eq_code, digitList_code fun ℓ => hd _ (List.getElem_mem ℓ.isLt),
    List.ofFn_getElem]







/-! ## Strings over a numbered alphabet -/

variable {α : Type} {b : ℕ} (e : α ≃ Fin b)

















/-- The code of a string of length `n` is less than `b^n`. -/
theorem codeStr_lt {n : ℕ} (u : Fin n → α) : codeStr e u < b ^ n :=
  code_lt fun ℓ => (e (u ℓ)).isLt

/-- Decoding undoes coding. -/
@[simp]
theorem decodeStr_codeStr [NeZero b] {n : ℕ} (u : Fin n → α) :
    decodeStr e n (codeStr e u) = u := by
  funext ℓ
  have hdigit := digit_code (d := fun ℓ => (e (u ℓ) : ℕ)) (fun ℓ => (e (u ℓ)).isLt) ℓ
  simp only [decodeStr, codeStr, hdigit, Fin.eta, Equiv.symm_apply_apply]













/-- The list of digits of the code of a string. -/
@[simp]
theorem digitList_codeStr {n : ℕ} (u : Fin n → α) :
    digitList b n (codeStr e u) = List.ofFn fun ℓ => (e (u ℓ) : ℕ) :=
  digitList_code fun ℓ => (e (u ℓ)).isLt












/-! ## The list of the digits of a string -/





section

variable {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ}

theorem length_digitsStr (u : Fin n → α) : (digitsStr e u).length = n := List.length_ofFn

theorem digitsStr_lt (u : Fin n → α) : ∀ d ∈ digitsStr e u, d < b := by
  intro d hd
  obtain ⟨ℓ, rfl⟩ := List.mem_ofFn.mp hd
  exact (e _).isLt

theorem digitsStr_injective : Function.Injective (digitsStr e : (Fin n → α) → List ℕ) :=
  fun _ _ h => funext fun ℓ => e.injective (Fin.ext (congrFun (List.ofFn_injective h) ℓ))

/-- Every list of n digits below b is the list of digits of a string. -/
theorem exists_digitsStr (l : List ℕ) (hl : l.length = n) (hd : ∀ d ∈ l, d < b) :
    ∃ u : Fin n → α, digitsStr e u = l := by
  subst hl
  refine ⟨fun ℓ => e.symm ⟨l[ℓ], hd _ (List.getElem_mem _)⟩, ?_⟩
  simp only [digitsStr, Equiv.apply_symm_apply]
  exact List.ofFn_getElem

/-- The digit at a level. -/
theorem getD_digitsStr (u : Fin n → α) (ℓ : Fin n) : (digitsStr e u).getD ℓ 0 = e (u ℓ) := by
  simp [digitsStr, List.getD_eq_getElem?_getD]

/-- A list with n members and the right digit at every level is the list of digits of the
string. -/
theorem digitsStr_eq_of_getD (u : Fin n → α) {l : List ℕ} (hl : l.length = n)
    (h : ∀ ℓ : Fin n, l.getD ℓ 0 = e (u ℓ)) : digitsStr e u = l := by
  refine List.ext_getElem (by rw [length_digitsStr, hl]) fun i hi _ => ?_
  rw [length_digitsStr] at hi
  rw [← List.getD_eq_getElem l 0, h ⟨i, hi⟩]
  simp only [digitsStr, List.getElem_ofFn]

/-- A statement on all positions of a digit a ≠ 0 is a statement on levels (beyond the end of the
list `getD` gives 0, so a position of the digit a is a level). -/
theorem forall_getD_digitsStr (u : Fin n → α) {a : ℕ} (ha : a ≠ 0) (P : ℕ → Prop) :
    (∀ j, (digitsStr e u).getD j 0 = a → P j) ↔ ∀ ℓ : Fin n, (e (u ℓ) : ℕ) = a → P ℓ := by
  refine ⟨fun h ℓ hℓ => h ℓ ((getD_digitsStr e u ℓ).trans hℓ), fun h j hj => ?_⟩
  have hjn : j < n := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by rw [length_digitsStr]; omega)] at hj
    exact ha hj.symm
  exact h ⟨j, hjn⟩ ((getD_digitsStr e u ⟨j, hjn⟩).symm.trans hj)

/-- The code is computed from the digits by Horner's rule. -/
theorem ofDigitList_digitsStr (u : Fin n → α) : ofDigitList b (digitsStr e u) = codeStr e u :=
  (code_eq_ofDigitList b fun ℓ => (e (u ℓ) : ℕ)).symm

end

end ThreeSumApsp

end
end

section


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/





























































































/-! Applying one of the five bijections gives the digit. -/





@[simp] theorem outEquiv_apply (z : OutVar) : outEquiv z = outIdx z := rfl





/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

/-- An output variable is inner exactly if its digit is 9. -/
theorem outVar_isInner_iff (z : OutVar) : z.IsInner ↔ (outIdx z : ℕ) = 9 := by
  revert z
  decide

/-- A term contributes to an output variable exactly if the variable has the digit 9 or the two
digits are equal. -/
theorem contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ (outIdx z : ℕ) = 9 ∨ (termIdx lam : ℕ) = (outIdx z : ℕ) := by
  revert lam z
  decide

/-- The digit of `z_ij` is `3 (i - 1) + (j - 1)`. -/
theorem outIdx_z (i j : Fin 3) : ((outIdx (.z i j) : Fin 10) : ℕ) = 3 * i + j := rfl




/-- The digit of `z₀` is 9. -/
theorem outIdx_z0 : ((outIdx .z0 : Fin 10) : ℕ) = 9 := rfl












/-! ## The coefficients of the linear forms, as tables -/





















/-- The table of the `φ_λ(s)` has 70 entries. -/
@[simp] theorem length_phiFlat : phiFlat.length = 70 := rfl

/-- The table of the `ψ_λ(t)` has 70 entries. -/
@[simp] theorem length_psiFlat : psiFlat.length = 70 := rfl













end ThreeSumApsp.Spec

end
end

section


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)






/-- The list has `b^n` entries. -/
theorem length_arrStr : (arrStr e a).length = b ^ n := by
  simp [arrStr]

/-- The entry of the list at a number below `b^n`. -/
theorem getD_arrStr_of_lt {c : ℕ} (hc : c < b ^ n) :
    (arrStr e a).getD c 0 = a (decodeStr e n c) := by
  rw [List.getD_eq_getElem _ _ (by rwa [length_arrStr])]
  simp [arrStr]

/-- The entry at a string is the entry of the list at its code. -/
theorem getD_arrStr (u : Fin n → α) : (arrStr e a).getD (codeStr e u) 0 = a u := by
  rw [getD_arrStr_of_lt e a (codeStr_lt e u), decodeStr_codeStr]









end

/-! ## The three kinds of arrays of Section 2 that the programs store -/


















/-- The list of an array on the leaves has `10^n` entries. -/
theorem length_arrT {n : ℕ} (enc : Leaf n → ℤ) : (arrT enc).length = 10 ^ n :=
  length_arrStr termEquiv enc










/-- The entry at a leaf is the entry of the list at its code. -/
theorem getD_arrT {n : ℕ} (enc : Leaf n → ℤ) (τ : Leaf n) :
    (arrT enc).getD (codeT τ) 0 = enc τ :=
  getD_arrStr termEquiv enc τ

end ThreeSumApsp.Spec

end
end

section


/-!
# The subsets of size `m` of `{1, …, L}`, enumerated

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  A subset is a *mask*: the list of `L` truth values saying
which levels belong to it, level 1 first (`maskSet`, `maskOf`).  The subsets of size `m` are
enumerated with those containing level 1 first, and so on recursively: `unrank L m r` is number `r`
in this order.

* The masks `unrank L m r` with `r < (L choose m)` have length `L` and `m` entries `true`, and they
  are distinct, because `rank` recovers `r` (`length_unrank`, `count_unrank`, `rank_unrank`).  So
  their sets of levels are distinct subsets of size `m` (`card_maskSet_unrank`,
  `eq_of_maskSet_unrank_eq`).
* A program lists them in a table without arithmetic, each mask from the one before it: the first
  mask is `true^m false^{L-m}` (`unrank_zero`), and two consecutive masks are
  `pre true false false^a true^b` and `pre false true true^b false^a` (`unrank_succ_shape`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The enumeration -/

























































/-! ## Masks and sets of levels -/








/-- The mask of a set of levels has one entry for each level. -/
theorem length_maskOf {L : ℕ} (Q : Finset (Fin L)) : (maskOf Q).length = L := by
  simp [maskOf]

/-- The entry of the mask at a level says whether the level belongs to the set. -/
theorem getD_maskOf {L n : ℕ} (Q : Finset (Fin L)) (hn : n < L) :
    (maskOf Q).getD n false = decide ((⟨n, hn⟩ : Fin L) ∈ Q) := by
  simp [maskOf, hn]


































/-! ## From one mask to the next -/











































































end ThreeSumApsp.Spec

end
end

section


/-!
# Cardinalities of finite sets

General facts about finite sets.

* A product with one value on `S` and another elsewhere (`Finset.prod_ite_mem_const`); two products
  that vanish unless one set lies in another (`Finset.prod_ite_ite_subset`,
  `Finset.prod_ite_ite_superset`); the number of sets of `k` elements inside a set or around a set
  (`Finset.sum_powersetCard_ite_subset`, `Finset.card_powersetCard_superset`).
* At most `c` elements of a set have a given quotient by `c` under an injective function
  (`Finset.card_filter_div_eq_le`).
* A finite subset of `Fin L` has `j` elements below its `j`-th lowest element
  (`Finset.card_filter_lt_orderEmbOfFin`, from `Finset.card_filter_lt_map` for any increasing
  sequence).

* A function `f : ι → α` has a property `p` at the place `i` if `p (f i)` holds. The number of
  functions `f` with `f i ∈ A i` that have `p` exactly at the places of a set `S` is a product over
  the places (`Finset.card_pi_places_eq`). The number of those that have `p` at exactly `k` places
  is the sum of these products over the sets `S` of `k` places (`Finset.card_pi_places_card`).
  Without the restriction to `A` it is a binomial coefficient times two powers
  (`Finset.card_places_card`).
-/

public section

namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product that takes the value `a` on `S` and `b` elsewhere. -/
theorem prod_ite_mem_const {M : Type*} [CommMonoid M] (S : Finset ι) (a b : M) :
    (∏ i, if i ∈ S then a else b) = a ^ #S * b ^ (Fintype.card ι - #S) := by
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter, filter_not,
    filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff, card_compl]

































































/-! ## The elements below a bound -/

/-- An increasing sequence has `j` members below its member number `j`. -/
theorem card_filter_lt_map {L k : ℕ} (f : Fin k ↪o Fin L) (j : Fin k) :
    ((Finset.univ.map f.toEmbedding).filter fun x : Fin L => (x : ℕ) < (f j : ℕ)).card = j := by
  have hbelow : (Finset.univ.filter ((fun x : Fin L => (x : ℕ) < (f j : ℕ)) ∘ f.toEmbedding))
      = Finset.Iio j := by
    ext i
    simp
  rw [Finset.filter_map, Finset.card_map, hbelow, Fin.card_Iio]

/-- The number of elements of `s` below its `j`-th lowest element is `j`. -/
theorem card_filter_lt_orderEmbOfFin {L k : ℕ} (s : Finset (Fin L)) (h : s.card = k) (j : Fin k) :
    (s.filter fun x : Fin L => (x : ℕ) < (s.orderEmbOfFin h j : ℕ)).card = j := by
  simpa only [Finset.map_orderEmbOfFin_univ] using card_filter_lt_map (s.orderEmbOfFin h) j

/-! ## Functions by the set of places with a property -/

variable {α : Type*} [Fintype α]










































end Finset

end
end

section


/-!
# Interleaving two strings of digits along a mask

A mask is a list of truth values, one for each level.  `weaveList mask outer inner` runs through the
levels and takes the next digit of `inner` at a level with the entry `true` and the next digit of
`outer` at a level with the entry `false`.  A program that forms the number with these digits by
Horner's rule needs one pass over the mask and two pointers: at level `ℓ` the pointer into `inner`
has passed as many digits as there are entries `true` among the first `ℓ` entries of the mask, and
the pointer into `outer` as many as there are entries `false` (`getD_weaveList`).
-/

@[expose] public section

namespace ThreeSumApsp









/-- `weaveList` has one digit for each level. -/
@[simp] theorem length_weaveList (mask : List Bool) (outer inner : List ℕ) :
    (weaveList mask outer inner).length = mask.length := by
  induction mask generalizing outer inner with
  | nil => simp [weaveList]
  | cons x mask ih => cases x <;> simp [weaveList, ih]

























/-- If the digits of both lists are below a positive number `b`, so are the interleaved digits. -/
theorem lt_of_mem_weaveList {b : ℕ} (hb : 0 < b) {mask : List Bool} {outer inner : List ℕ}
    (houter : ∀ d ∈ outer, d < b) (hinner : ∀ d ∈ inner, d < b) :
    ∀ d ∈ weaveList mask outer inner, d < b := by
  intro d hd
  obtain ⟨ℓ, hℓ, rfl⟩ := List.getElem_of_mem hd
  rw [← List.getD_eq_getElem _ 0 hℓ, getD_weaveList]
  split_ifs
  · exact List.getD_of_forall_mem (p := (· < b)) hb hinner _
  · exact List.getD_of_forall_mem (p := (· < b)) hb houter _
  · exact hb

end ThreeSumApsp

end
end

section


/-!
# One computable layout of the tiling

The statements of Section 2.3.4 about the tiling hold for every `Layout`: every numbering of the
rows and columns of a block by strings, and every table of `K₀²` subsets of size `m`.  A
program needs one layout that it can compute.  In `stdLayout` the rows and columns of a block are
numbered by the base-3 codes of their strings, the columns of `X` by base-4 codes, and the block
product `(g, h)` of a tile gets the subset number `g K₀ + h` of the enumeration `unrank`.

The strings of Lemma 9 are glued from an inner part, at the levels of a set `Q`, and an outer part,
at the other levels.  Their codes are formed digit by digit:

1. the digits of a glued string are the digits of its two parts, interleaved along the mask of `Q`
   by `weaveList` (`ofFn_glue`), because the `k`-th level of `Q` has exactly `k` levels of `Q` below
   it (`Finset.card_filter_lt_orderEmbOfFin`, `count_take_maskOf`);
2. so `outDigitsOfPos` lists the digits, and `outCodeOfPos` is the code, of the output string of a
   position `(I, J)` (Section 2.4.4, `codeO_outStrOfPos`, `digitList_outCodeOfPos`);
3. and `gluedCode` is the code of the left or right string with given parts (`codeL_leftStrOf`,
   `codeR_rightStrOf`).  The input array of a band holds the entries of `X` or `Y` at these codes
   and 0 elsewhere (`bandArrayL_at`, `bandArrayL_eq_zero`, and the same for `R`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The layout -/





















section
variable {L m : ℕ} (hmL : m ≤ L)

/-- The row with number `k` of a block is indexed by the string with code `k`. -/
private theorem codeOuter_rowIdx (k : Fin (N0 L m)) : codeOuter ((stdLayout hmL).rowIdx k) = k :=
  congrArg Fin.val ((codeEquiv 3 (L - m)).apply_symm_apply k)





/-- The string that indexes the row with number `k` of a block consists of the base-3 digits of
`k`. -/
private theorem ofFn_rowIdx (k : Fin (N0 L m)) :
    (List.ofFn fun ℓ => ((stdLayout hmL).rowIdx k ℓ : ℕ)) = digitList 3 (L - m) k :=
  (digitList_codeStr (Equiv.refl (Fin 3)) _).symm.trans
    (congrArg (digitList 3 (L - m)) (codeOuter_rowIdx hmL k))

/-- The string that indexes the column with number `k` of a block consists of the base-3 digits of
`k`. -/
private theorem ofFn_colIdx (k : Fin (N0 L m)) :
    (List.ofFn fun ℓ => ((stdLayout hmL).colIdx k ℓ : ℕ)) = digitList 3 (L - m) k :=
  ofFn_rowIdx hmL k






/-- The mask of the subset of a block product. -/
private theorem maskOf_table (gh : Fin (K0 L m) × Fin (K0 L m)) :
    maskOf ((stdLayout hmL).table gh) = unrank L m (gh.1 * K0 L m + gh.2) :=
  maskOf_maskSet _ (length_unrank _ _ _)

end

/-! ## Counting the levels of a set below a level -/

/-- The entries `true` (and `false`) among the first `n` entries of the mask of `Q` count the levels
of `Q` (and outside `Q`) below `n`. -/
private theorem count_take_maskOf {L : ℕ} (Q : Finset (Fin L)) (n : ℕ) :
    ((maskOf Q).take n).count true = (Q.filter fun x : Fin L => (x : ℕ) < n).card ∧
      ((maskOf Q).take n).count false = (Qᶜ.filter fun x : Fin L => (x : ℕ) < n).card := by
  constructor <;> rw [maskOf, List.count_take_ofFn] <;> congr 1 <;> ext x <;> simp [and_comm]

/-! ## The code of a glued string -/

/-- The digits of a string glued from `inner` at the levels of `Q` and `outer` at the other levels
are interleaved along the mask of `Q`. -/
theorem ofFn_glue {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (inner : Fin m → ℕ)
    (outer : Fin (L - m) → ℕ) :
    List.ofFn (glue Q hQ inner outer)
      = weaveList (maskOf Q) (List.ofFn outer) (List.ofFn inner) := by
  refine List.ext_getElem (by simp [length_maskOf]) fun n hn hweave => ?_
  replace hn : n < L := by simpa using hn
  obtain ⟨htrue, hfalse⟩ := count_take_maskOf Q n
  rw [List.getElem_ofFn, ← List.getD_eq_getElem _ 0 hweave, getD_weaveList,
    if_pos (by rwa [length_maskOf]), htrue, hfalse, getD_maskOf Q hn]
  by_cases hmem : (⟨n, hn⟩ : Fin L) ∈ Q
  · -- Level `n` is the `k`-th level of `Q`, and `k` levels of `Q` lie below it.
    obtain ⟨k, hk⟩ := exists_innerLevel Q hQ hmem
    have hcount := Finset.card_filter_lt_orderEmbOfFin Q hQ k
    rw [show ((Q.orderEmbOfFin hQ k : Fin L) : ℕ) = n from congrArg Fin.val hk] at hcount
    rw [← hk, glue_innerLevel, hk, hcount]
    simp [hmem]
  · -- Level `n` is the `k`-th level outside `Q`, and `k` levels outside `Q` lie below it.
    obtain ⟨k, hk⟩ := exists_outerLevel Q hQ hmem
    have hcount := Finset.card_filter_lt_orderEmbOfFin Qᶜ (card_compl_of_card_eq Q hQ) k
    rw [show ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ) k : Fin L) : ℕ) = n from
      congrArg Fin.val hk] at hcount
    rw [← hk, glue_outerLevel, hk, hcount]
    simp [hmem]

/-- The code of a string of digits glued from `inner` at the levels of `Q` and `outer` at the other
levels, by Horner's rule on the interleaved digits. -/
theorem code_glue (b : ℕ) {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (inner : Fin m → ℕ)
    (outer : Fin (L - m) → ℕ) :
    code b (glue Q hQ inner outer)
      = ofDigitList b (weaveList (maskOf Q) (List.ofFn outer) (List.ofFn inner)) := by
  rw [code_eq_ofDigitList, ofFn_glue]

/-! ## The digits and the code of the output string of a position -/

section outDigits
variable {m ℓ : ℕ} {mask : List Bool} {rI rJ : List ℕ}







/-- An output string has one digit for each level. -/
@[simp] theorem length_outDigits : (outDigits m mask rI rJ).length = mask.length :=
  length_weaveList ..



















/-- The digits of an output string are below 10. -/
theorem lt_of_mem_outDigits (hI : ∀ x ∈ rI, x < 3) (hJ : ∀ y ∈ rJ, y < 3) :
    ∀ d ∈ outDigits m mask rI rJ, d < 10 := by
  refine lt_of_mem_weaveList (by norm_num) (fun d hd => ?_) fun d hd => ?_
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    rw [List.length_zipWith, lt_min_iff] at hi
    have hx := hI _ (List.getElem_mem hi.1)
    have hy := hJ _ (List.getElem_mem hi.2)
    rw [List.getElem_zipWith]
    omega
  · rw [List.eq_of_mem_replicate hd]
    norm_num

end outDigits

/-- The code of the output string with inner set `Q`, row `r` and column `c`. -/
theorem codeO_outStrOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (r c : OuterStr L m) :
    codeO (outStrOf Q hQ r c)
      = ofDigitList 10 (outDigits m (maskOf Q) (List.ofFn fun k => (r k : ℕ))
          (List.ofFn fun k => (c k : ℕ))) := by
  rw [outStrOf, codeO, codeStr,
    map_glue Q hQ (fun z => ((outEquiv z : Fin 10) : ℕ)), code_glue, outDigits,
    ← List.ofFn_const]
  simp only [outEquiv_apply, outIdx_z, outIdx_z0]
  congr 2
  exact List.ext_getElem (by simp) fun n _ _ => by simp


















/-- The output string of a position has `L` digits. -/
@[simp] theorem length_outDigitsOfPos (L m I J : ℕ) : (outDigitsOfPos L m I J).length = L := by
  rw [outDigitsOfPos, length_outDigits, length_unrank]

/-- The digits of the code of the output string of a position. -/
theorem digitList_outCodeOfPos (L m I J : ℕ) :
    digitList 10 L (outCodeOfPos L m I J) = outDigitsOfPos L m I J := by
  have hdigits := digitList_ofDigitList (outDigitsOfPos L m I J)
    (lt_of_mem_outDigits (fun _ => lt_of_mem_digitList (by norm_num))
      fun _ => lt_of_mem_digitList (by norm_num))
  rwa [length_outDigitsOfPos] at hdigits

/-- `outCodeOfPos` computes the code of the output string of a position, for the computable layout.
-/
theorem codeO_outStrOfPos {L m : ℕ} (hmL : m ≤ L) (I J : ℕ) :
    codeO (outStrOfPos (stdLayout hmL) I J) = outCodeOfPos L m I J := by
  rw [outStrOfPos, codeO_outStrOf, outCodeOfPos, outDigitsOfPos, maskOf_table, ofFn_rowIdx,
    ofFn_colIdx]
  -- By definition the block of `I` is `I / N₀ % K₀`, and its offset is `I % N₀`.
  rfl

/-! ## The codes of the left and right strings, and the input arrays of the bands -/





























































section
variable {L m N : ℕ} (hmL : m ≤ L)









































end




















































end ThreeSumApsp.Spec

end
end

section


/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- Cell j of the directory, with the address in the form in which the evaluation of mem[b0 + j]
meets it. -/
theorem SharedReady.dir_read (h : SharedReady p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ ((b0 : ℤ) + j).toNat = ((dirList p aX aY b0).getD j 0 : ℕ) := by
  rw [toNat_natCast_add_natCast]
  exact h.dir.read (by simpa [dirList] using hj)
















/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ (by omega) (by omega)
      psi := h.psi.congr fun i hi => he _ (by omega) (by omega)
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ (by omega) ?_
      band := fun I hI => (he _ (by omega) (by omega)).trans (h.band I hI)
      block := fun I hI => (he _ (by omega) (by omega)).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ (by omega) ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ (by omega) ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

/-- What the shared stage leaves behind is kept by a memory that agrees on the cells of the shared
block, but for cell 31 of the directory, which the shared stage does not use. -/
theorem SharedReady.congr (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [Spec.length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [Spec.length_arrT] at hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)








end Light.Sec2

end
end

section


/-!
# Section 2.4.3, first half: the orders of the leaves and equation (5)

A leaf that contributes to an output string with inner set `Q` is free at the `m` levels of `Q` and
fixed at the other levels.  Its order is `m` minus the number of levels at which it chooses `P₀`.

* One level.  A term contributes to `z` exactly if `z = z₀` or the term is the private term of `z`
  (`Term.contributes_iff`), so a leaf contributing to a string chooses `P₀` only at levels of the
  inner set (`P0Levels_subset`).  The numbers of terms of each kind that contribute to a variable,
  and of variables of each kind to which a term contributes, are read off the ten terms.
* Counts.  `10^m` leaves contribute to a string: ten terms for each level of `Q`
  (`card_filter_contributes`).  The other counts sort strings by the set of levels at which they
  have a letter of a given kind (`Finset.card_pi_places_card`, `Finset.card_places_card`): `α_d` of
  the leaves contributing to a string have order `d` (`sec2_card_contributing_of_order`), the whole
  tree has `β_d` leaves of order `d` (`card_filter_order_eq`), with `β₀ = M` (`beta_zero_eq_M`), and
  a leaf of order `d` contributes to `binom(L-m+d, d)` strings (`sec2_card_outStr_of_leaf`). Figure
  6 shows these numbers for `L = 6` and `m = 2` (`figure_6`).
* Equation (5): the quotient `β_d / β_{d-1}` comes from the recurrence of the binomial coefficients
  (`Equation5.ratio_nat`, `eq_5_ratio`); for `L = 19m` it is less than `1/2` (`eq_5_bound`); so
  `β_d ≤ 2^{-d} M` by induction on `d` (`eq_5`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### One level: which terms contribute to which variables -/

/-- The private term of `z` is `P₀` exactly if `z = z₀`. -/
theorem OutVar.privateTerm_eq_P0_iff (z : OutVar) : z.privateTerm = Term.P0 ↔ z.IsInner := by
  cases z <;> simp [OutVar.IsInner, OutVar.privateTerm]






















/-- The number of terms contributing to `z`: ten if `z = z₀`, one if `z = z_ij`. -/
private theorem card_contributing_term (z : OutVar) :
    (univ.filter fun lam : Term => lam.Contributes z).card = if z.IsInner then 10 else 1 := by
  decide +revert













/-! ### The order of a leaf -/

/-- Membership in the set of levels at which a leaf chooses `P₀`. -/
@[simp]
theorem mem_P0Levels {L : ℕ} {τ : Leaf L} {ℓ : Fin L} : ℓ ∈ P0Levels τ ↔ τ ℓ = Term.P0 := by
  simp [P0Levels]

/-- Membership in the inner set of an output string. -/
@[simp]
theorem mem_innerSetO {L : ℕ} {η : OutStr L} {ℓ : Fin L} : ℓ ∈ innerSetO η ↔ (η ℓ).IsInner := by
  simp [innerSetO]

/-- Section 2.4.3: "A leaf contributing to an output string chooses P₀ only at levels of the output
string's inner set". -/
theorem P0Levels_subset {L : ℕ} {τ : Leaf L} {w : OutStr L} (h : Leaf.Contributes τ w) :
    P0Levels τ ⊆ innerSetO w := by
  intro ℓ hℓ
  rw [mem_P0Levels] at hℓ
  rw [mem_innerSetO]
  rcases (Term.contributes_iff _ _).mp (h ℓ) with hinner | hprivate
  · exact hinner
  · exact (OutVar.privateTerm_eq_P0_iff _).mp (hprivate.symm.trans hℓ)

/-- Section 2.4.3: "so its order is at least 0." -/
theorem order_nonneg {L m : ℕ} {w : OutStr L} (hw : (innerSetO w).card = m) {τ : Leaf L}
    (h : Leaf.Contributes τ w) : 0 ≤ order m τ := by
  have hc := card_le_card (P0Levels_subset h)
  unfold order
  omega













/-! ### The counts -/

/-- Section 2.4.3: "A single output string has 10^m […] leaves contributing to it." -/
theorem card_filter_contributes {L m : ℕ} (w : OutStr L) (hw : (innerSetO w).card = m) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w).card = 10 ^ m := by
  -- Ten terms contribute to `z₀` and one to `z_ij`.
  simp only [Leaf.filter_contributes_eq_piFinset, Fintype.card_piFinset,
    card_contributing_term]
  rw [prod_ite, prod_const, prod_const_one, mul_one, ← hw]
  rfl


















































































































































































end ThreeSumApsp

end
end

section


/-!
# Cubes and boxes (Section 4.2)

A cube is a string of `L` symbols, each of them one of the ten terms or a star, and its leaves are
obtained by replacing each star by any term. A box is a cube with at most `m - t` symbols `P₀` or
stars whose stars are all below its symbols `P₀`. This file proves what the paper says about cubes
and boxes before it turns to the boxes of one output string, in this order:

* from "Notions from Section 2": `M ≤ 10^L` (`M_le_ten_pow`);
* a cube with `e` stars has `10^e` leaves (`Cube.card_leaves`);
* the leaves, the stars and the symbols `P₀` of three cubes: a leaf read as a cube (`Cube.ofLeaf`),
  a cube with a star replaced by a term (`Cube.replace`), and a leaf with stars put at a set of
  levels (`Cube.starAt`); every cube that Section 4.2 makes from a leaf is of this third form;
* the leaves contributing to an output string `η` (w in the paper) are the leaves of the cube of `η`
  (`mem_leaves_cubeOf`), so the entry `(X_Q Y_Q)[η]` is the value of that cube
  (`mul_apply_eq_val_cubeOf`); Section 4.2 starts from this remark, and nothing else rests on it;
* the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has `P₀`
  or a star (`P0Levels_starsToP0`);
* a box only contains leaves of order at least `t` (`le_order_of_mem_leaves`);
* the `k` lowest levels of a set `S` lie below the other levels of `S` (`lowest_lt`), this property
  characterizes them (`eq_lowest_of_lt`), and there are `min k |S|` of them (`card_lowest`);
* a box is a leaf with its lowest symbols `P₀` replaced by stars (`eq_starLowest_starsToP0`), and
  every cube obtained in this way from a leaf with at most `m - t` symbols `P₀` is a box
  (`isBox_starLowest`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}








/-! ### Cubes and their leaves (Section 4.2) -/

/-- Membership in the set of leaves of a cube, level by level. -/
@[simp]
theorem Cube.mem_leaves {π : Cube L} {τ : Leaf L} :
    τ ∈ Cube.leaves π ↔ ∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ) := by
  simp only [Cube.leaves, mem_filter, mem_univ, true_and]
  rfl

/-- Where a cube has a term, its leaves have that term. -/
theorem Cube.eq_of_mem_leaves {π : Cube L} {τ : Leaf L} (hτ : τ ∈ Cube.leaves π) {ℓ : Fin L}
    {lam : Term} (h : π ℓ = CubeSymbol.term lam) : τ ℓ = lam := by
  simpa [h, eq_comm] using Cube.mem_leaves.1 hτ ℓ

/-- Membership in the set of star levels of a cube. -/
@[simp]
theorem Cube.mem_starLevels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ Cube.starLevels π ↔ π ℓ = CubeSymbol.star := by
  simp [Cube.starLevels]

/-- Membership in the set of levels at which a cube has `P₀`. -/
@[simp]
theorem Cube.mem_P0Levels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ Cube.P0Levels π ↔ π ℓ = CubeSymbol.term Term.P0 := by
  simp [Cube.P0Levels]

/-- No level of a cube has both a star and `P₀`. -/
theorem Cube.disjoint_starLevels_P0Levels (π : Cube L) :
    Disjoint (Cube.starLevels π) (Cube.P0Levels π) := by
  rw [disjoint_left]
  intro ℓ hstar hP0
  rw [Cube.mem_starLevels] at hstar
  rw [Cube.mem_P0Levels, hstar] at hP0
  cases hP0






/-- The leaves of a cube form a product set: the choices at the levels are independent. -/
private lemma leaves_eq_piFinset (π : Cube L) :
    Cube.leaves π = Fintype.piFinset fun ℓ => symbolTerms (π ℓ) := by
  ext τ
  rw [Cube.mem_leaves, Fintype.mem_piFinset]
  refine forall_congr' fun ℓ => ?_
  cases h : π ℓ <;> simp [symbolTerms, eq_comm]

/-- Section 4.2: "a cube with e stars has 10^e leaves". -/
theorem Cube.card_leaves (π : Cube L) :
    (Cube.leaves π).card = 10 ^ (Cube.starLevels π).card := by
  have hcard : ∀ ℓ, (symbolTerms (π ℓ)).card = if ℓ ∈ Cube.starLevels π then 10 else 1 := by
    intro ℓ
    cases h : π ℓ <;> simp [symbolTerms, h, card_term]
  rw [leaves_eq_piFinset, Fintype.card_piFinset]
  simp only [hcard]
  rw [prod_ite_mem_const, one_pow, mul_one]

/-! ### A leaf as a cube without stars (Section 4.2) -/





/-- The only leaf of the cube without stars made from `τ` is `τ`. -/
@[simp]
theorem Cube.leaves_ofLeaf (τ : Leaf L) : Cube.leaves (Cube.ofLeaf τ) = {τ} := by
  ext σ
  simp [Cube.ofLeaf, funext_iff, eq_comm]

/-- The cube made from a leaf has no stars. -/
@[simp]
theorem Cube.starLevels_ofLeaf (τ : Leaf L) : Cube.starLevels (Cube.ofLeaf τ) = ∅ := by
  ext ℓ
  simp [Cube.ofLeaf]

/-- The cube made from a leaf has `P₀` where the leaf chooses `P₀`. -/
@[simp]
theorem Cube.P0Levels_ofLeaf (τ : Leaf L) :
    Cube.P0Levels (Cube.ofLeaf τ) = ThreeSumApsp.P0Levels τ := by
  ext ℓ
  simp [Cube.ofLeaf]

/-! ### Replacing a star by a term (proof of Lemma 29) -/

/-- The leaves of `π[ℓ ← λ]`, for a star of `π` at level `ℓ`, are the leaves of `π` that choose `λ`
at level `ℓ`. -/
theorem Cube.mem_leaves_replace {π : Cube L} {ℓ : Fin L} (hℓ : π ℓ = CubeSymbol.star)
    (lam : Term) (τ : Leaf L) :
    τ ∈ Cube.leaves (Cube.replace π ℓ lam) ↔ τ ∈ Cube.leaves π ∧ τ ℓ = lam := by
  rw [Cube.mem_leaves, Cube.mem_leaves, Cube.replace,
    Function.forall_update_iff π fun k s => s = CubeSymbol.star ∨ s = CubeSymbol.term (τ k)]
  constructor
  · rintro ⟨hlam, h⟩
    refine ⟨fun k => ?_, by simpa [eq_comm] using hlam⟩
    by_cases hk : k = ℓ
    · exact Or.inl (hk ▸ hℓ)
    · exact h k hk
  · rintro ⟨h, rfl⟩
    exact ⟨Or.inr rfl, fun k _ => h k⟩
















/-! ### Putting stars into a leaf (Section 4.2) -/





/-- `τ` is a leaf of the cube obtained from `τ` by putting stars at some levels. -/
theorem Cube.mem_leaves_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    τ ∈ Cube.leaves (Cube.starAt F τ) :=
  Cube.mem_leaves.2 fun ℓ => (em (ℓ ∈ F)).imp (if_pos ·) (if_neg ·)

/-- The stars of `Cube.starAt F τ` are at the levels of `F`. -/
@[simp]
theorem Cube.starLevels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    Cube.starLevels (Cube.starAt F τ) = F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- The symbols `P₀` of `Cube.starAt F τ` are at the levels outside `F` at which `τ` chooses `P₀`.
-/
@[simp]
theorem Cube.P0Levels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    Cube.P0Levels (Cube.starAt F τ) = ThreeSumApsp.P0Levels τ \ F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- If `τ` chooses `P₀` at the levels of `F`, then replacing the stars of `Cube.starAt F τ` with
`P₀` gives back `τ`. -/
theorem Cube.starsToP0_starAt {F : Finset (Fin L)} {τ : Leaf L}
    (h : F ⊆ ThreeSumApsp.P0Levels τ) :
    Cube.starsToP0 (Cube.starAt F τ) = τ := by
  funext ℓ
  unfold Cube.starsToP0 Cube.starAt
  split_ifs with hℓ
  · exact (ThreeSumApsp.mem_P0Levels.1 (h hℓ)).symm
  · rfl

/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/




























/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/








/-- A cube is the leaf obtained by replacing its stars with `P₀`, with stars at the star levels of
the cube. -/
theorem Cube.starAt_starLevels_starsToP0 (π : Cube L) :
    Cube.starAt (Cube.starLevels π) (Cube.starsToP0 π) = π := by
  funext ℓ
  unfold Cube.starAt Cube.starsToP0
  cases h : π ℓ <;> simp [h]

/-- Section 4.2: "a cube without stars is a single leaf", namely the leaf `Cube.starsToP0 π`. -/
theorem Cube.eq_ofLeaf_of_starLevels_eq_empty (π : Cube L) (hπ : Cube.starLevels π = ∅) :
    π = Cube.ofLeaf (Cube.starsToP0 π) := by
  conv_lhs => rw [← Cube.starAt_starLevels_starsToP0 π, hπ]
  funext ℓ
  simp [Cube.starAt, Cube.ofLeaf]

/-- The leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has a
star or `P₀`. -/
theorem P0Levels_starsToP0 (π : Cube L) :
    P0Levels (Cube.starsToP0 π) = Cube.starLevels π ∪ Cube.P0Levels π := by
  ext ℓ
  rw [mem_P0Levels, mem_union, Cube.mem_starLevels, Cube.mem_P0Levels]
  unfold Cube.starsToP0
  cases h : π ℓ <;> simp

/-- Proof of Lemma 29: the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` at
as many levels as the cube has symbols `P₀` or stars. -/
theorem card_P0Levels_starsToP0 (π : Cube L) :
    (P0Levels (Cube.starsToP0 π)).card = (Cube.starLevels π).card + (Cube.P0Levels π).card := by
  rw [P0Levels_starsToP0, card_union_of_disjoint (Cube.disjoint_starLevels_P0Levels π)]

/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/

/-- Section 4.2: "the leaves of order at least t, i.e., the leaves that choose P₀ at most m - t
times". -/
theorem le_order_iff {m t : ℕ} (ht : t ≤ m) (τ : Leaf L) :
    (t : ℤ) ≤ order m τ ↔ (P0Levels τ).card ≤ m - t := by
  unfold order
  omega

/-- Section 4.2: "A leaf of π chooses P₀ at the f - e levels where π has P₀ and possibly at some of
its e star levels", and nowhere else. -/
theorem P0Levels_subset_of_mem_leaves {π : Cube L} {τ : Leaf L} (hτ : τ ∈ Cube.leaves π) :
    P0Levels τ ⊆ Cube.P0Levels π ∪ Cube.starLevels π := by
  intro ℓ hℓ
  rw [mem_P0Levels] at hℓ
  rw [mem_union, Cube.mem_P0Levels, Cube.mem_starLevels, ← hℓ]
  exact (Cube.mem_leaves.1 hτ ℓ).symm

/-- Section 4.2: "so a box only contains leaves of order at least t". -/
theorem le_order_of_mem_leaves {m t : ℕ} (ht : t ≤ m) {π : Cube L} (hπ : IsBox m t π)
    {τ : Leaf L} (hτ : τ ∈ Cube.leaves π) : (t : ℤ) ≤ order m τ := by
  rw [le_order_iff ht]
  calc (P0Levels τ).card ≤ (Cube.P0Levels π ∪ Cube.starLevels π).card :=
        card_le_card (P0Levels_subset_of_mem_leaves hτ)
    _ ≤ (Cube.P0Levels π).card + (Cube.starLevels π).card := card_union_le _ _
    _ ≤ m - t := (add_comm _ _).trans_le hπ.1

/-! ### The `k` lowest levels of a set (Section 4.2) -/

/-- The `k` lowest levels of `S` are levels of `S`. -/
theorem lowest_subset (k : ℕ) (S : Finset (Fin L)) : lowest k S ⊆ S :=
  filter_subset _ _

/-- Membership in the set of the `k` lowest levels of `S`. -/
private lemma mem_lowest {k : ℕ} {S : Finset (Fin L)} {ℓ : Fin L} :
    ℓ ∈ lowest k S ↔ ℓ ∈ S ∧ (S.filter fun ℓ' => ℓ' < ℓ).card < k := by
  simp [lowest]

/-- The number of levels of `S` below a level of `S` grows strictly with the level. -/
private lemma card_below_strictMonoOn (S : Finset (Fin L)) :
    StrictMonoOn (fun ℓ => (S.filter fun x => x < ℓ).card) S := by
  intro ℓ hℓ ℓ' _ hlt
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · exact mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.trans hlt⟩
  · exact lt_irrefl ℓ (mem_filter.1 (hsub (mem_filter.2 ⟨hℓ, hlt⟩))).2

/-- Each of the `k` lowest levels of `S` is below every other level of `S`. -/
theorem lowest_lt {k : ℕ} {S : Finset (Fin L)} {ℓ ℓ' : Fin L} (hℓ : ℓ ∈ lowest k S)
    (hℓ' : ℓ' ∈ S \ lowest k S) : ℓ < ℓ' := by
  obtain ⟨hS, hbelow⟩ := mem_lowest.1 hℓ
  obtain ⟨hS', hnot⟩ := mem_sdiff.1 hℓ'
  -- otherwise `ℓ' ≤ ℓ` would have at most as many levels of `S` below it as `ℓ`, fewer than `k`
  by_contra hlt
  exact hnot (mem_lowest.2
    ⟨hS', ((card_below_strictMonoOn S).monotoneOn hS' hS (not_lt.1 hlt)).trans_lt hbelow⟩)



















/-- The numbers of levels of `S` below the levels of `S` are `0, …, |S| - 1`. -/
private lemma image_card_below (S : Finset (Fin L)) :
    (S.image fun ℓ => (S.filter fun x => x < ℓ).card) = range S.card := by
  refine eq_of_subset_of_card_le (fun n hn => ?_) ?_
  · obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hn
    exact mem_range.2
      (card_lt_card ⟨filter_subset _ _, fun hsub => lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2⟩)
  · rw [card_image_of_injOn (card_below_strictMonoOn S).injOn, card_range]

/-- The set of the `k` lowest levels of `S` has `min k |S|` elements. -/
theorem card_lowest (k : ℕ) (S : Finset (Fin L)) : (lowest k S).card = min k S.card := by
  -- The map from a level to the number of levels of `S` below it is injective on `S`, its image is
  -- `{0, …, |S| - 1}`, and by definition `lowest k S` is the preimage of the numbers below `k`.
  have hinj := (card_below_strictMonoOn S).injOn.mono (coe_subset.2 (lowest_subset k S))
  have hrange : ((range S.card).filter fun n => n < k) = range (min k S.card) := by
    ext n
    simp only [mem_filter, mem_range, lt_min_iff, and_comm]
  rw [← card_image_of_injOn hinj, ← card_range (min k S.card), ← hrange, ← image_card_below,
    filter_image]
  rfl

/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/





/-- The stars of `starLowest e τ` are at the `e` lowest levels at which `τ` chooses `P₀`. -/
theorem starLevels_starLowest (e : ℕ) (τ : Leaf L) :
    Cube.starLevels (starLowest e τ) = lowest e (P0Levels τ) :=
  Cube.starLevels_starAt _ τ

/-- The symbols `P₀` of `starLowest e τ` are at the other levels at which `τ` chooses `P₀`. -/
theorem P0Levels_starLowest (e : ℕ) (τ : Leaf L) :
    Cube.P0Levels (starLowest e τ) = P0Levels τ \ lowest e (P0Levels τ) :=
  Cube.P0Levels_starAt _ τ

/-- Replacing the stars of `starLowest e τ` with `P₀` gives back `τ`. -/
theorem starsToP0_starLowest (e : ℕ) (τ : Leaf L) : Cube.starsToP0 (starLowest e τ) = τ :=
  Cube.starsToP0_starAt (lowest_subset _ _)

/-- Section 4.2: "By (ii), a box is obtained from a leaf of order at least t by replacing its e
lowest symbols P₀ (rather than an arbitrary subset of them) by stars." The leaf is
`Cube.starsToP0 π`, and only condition (ii) is used. -/
theorem eq_starLowest_starsToP0 (π : Cube L)
    (h : ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ') :
    π = starLowest (Cube.starLevels π).card (Cube.starsToP0 π) := by
  have hlow : Cube.starLevels π =
      lowest (Cube.starLevels π).card (P0Levels (Cube.starsToP0 π)) := by
    refine eq_lowest_of_lt ?_ fun ℓ hℓ ℓ' hℓ' => h ℓ hℓ ℓ' ?_
    · rw [P0Levels_starsToP0]
      exact subset_union_left
    · rw [P0Levels_starsToP0, mem_sdiff, mem_union] at hℓ'
      tauto
  rw [starLowest, ← hlow, Cube.starAt_starLevels_starsToP0]

/-- The converse: replacing the `e` lowest symbols `P₀` of a leaf with at most `m - t` symbols `P₀`
by stars gives a box. -/
theorem isBox_starLowest (m t e : ℕ) (τ : Leaf L) (hτ : (P0Levels τ).card ≤ m - t) :
    IsBox m t (starLowest e τ) := by
  rw [IsBox, ← card_P0Levels_starsToP0, starsToP0_starLowest, starLevels_starLowest,
    P0Levels_starLowest]
  exact ⟨hτ, fun ℓ hℓ ℓ' hℓ' => lowest_lt hℓ hℓ'⟩

end ThreeSumApsp

end
end

section


/-!
# Lemmas 27 and 28: the boxes of an output string (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. A leaf `τ`
contributing to `η` chooses `P₀` at the set `Z` of levels of `Q`; `V` is `Z` padded from the bottom
to `m - t` levels; `F_V` is the longest initial segment of `Q` contained in `V`; and `𝓑_V` is the
set of the cubes with stars at `F_V`, with `P₀` at `V ∖ F_V`, with one of the nine terms `P_ij` at
each level of `Q ∖ V`, and with the terms of the private leaf of `η` outside `Q`. The file follows
the paper's order, except that Figure 10 comes after the definitions that it illustrates.

* *The sets `Z`, `V`, `F_V`.* The set `V` has `m - t` levels (`card_Vof`). The definition of `F_V`
  is the printed one (`FV_eq`). The condition `V ∖ F_V ⊆ Z` says that every level of `V ∖ Z` is
  below every level of `Q ∖ V` (`sdiff_FV_subset_iff`); this carries Lemma 27.
* *The sets `𝓑_V`.* They have `9^t` cubes (`card_BV`), which are boxes (`BV_isBox`), and they are
  disjoint (`BV_pairwiseDisjoint`). The box of a leaf is in `𝓑_V` for the `V` of the leaf
  (`boxOfLeaf_mem_BV`). A leaf contributing to `η` is a leaf of a box of `𝓑_V` if and only if
  `V ∖ F_V ⊆ Z ⊆ V` (`exists_mem_BV_leaf_iff`), and then of exactly one (`BV_leaf_unique`).
* *Figure 10*, for `m = 4` and `t = 2` (`figure_10_counts`, `figure_10_rows`, `figure_10_Vof`).
* **Lemma 27** (`lemma_27`): for `|Z| ≤ m - t`, the only `V` of `m - t` levels with
  `V ∖ F_V ⊆ Z ⊆ V` is `Z` padded from the bottom.
* **Lemma 28**: the leaves of order at least `t` contributing to `η` are the leaves of the boxes of
  the sets `𝓑_V` (`lemma_28_leaves`), and each of them lies in exactly one box (`lemma_28_unique`).
  So a sum over the leaves contributing to `η` splits into the leaves of order below `t` and the
  boxes (`Lemma28.sum_contributing`). For the products at the leaves this is the equation of the
  lemma (`lemma_28`), and for the constant 1 it counts the leaves (`Lemma28.card_leaves`). The
  numbers of terms are `∑_{d < t} α_d` and `α_t` (`lemma_28_counts`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}

/-! ### The sets `Z`, `V` and `F_V` (Section 4.2) -/





/-- Section 2.4.3: a leaf contributes to `η` exactly if it agrees with the private leaf of `η`
outside the inner set. -/
private lemma contributes_iff_eq_privateLeaf (η : OutStr L) (τ : Leaf L) :
    Leaf.Contributes τ η ↔ ∀ ℓ, ℓ ∉ innerSetO η → τ ℓ = privateLeaf η ℓ := by
  refine forall_congr' fun ℓ => ?_
  rw [Term.contributes_iff, mem_innerSetO]
  exact or_iff_not_imp_left

/-- Outside the inner set the private leaf does not choose `P₀`. -/
private lemma privateLeaf_ne_P0 {η : OutStr L} {ℓ : Fin L} (hℓ : ℓ ∉ innerSetO η) :
    privateLeaf η ℓ ≠ Term.P0 :=
  fun h => hℓ (mem_innerSetO.2 ((OutVar.privateTerm_eq_P0_iff _).1 h))

/-- `Z` is a set of levels of `Q`. -/
private lemma Zof_subset (Q : Finset (Fin L)) (τ : Leaf L) : Zof Q τ ⊆ Q :=
  filter_subset _ _

/-- A leaf contributing to `η` chooses `P₀` exactly at the levels of `Z`. -/
private lemma P0Levels_eq_Zof (η : OutStr L) (τ : Leaf L) (hτ : Leaf.Contributes τ η) :
    P0Levels τ = Zof (innerSetO η) τ := by
  ext ℓ
  rw [Zof, mem_filter, mem_P0Levels]
  exact ⟨fun h => ⟨P0Levels_subset hτ (mem_P0Levels.2 h), h⟩, fun h => h.2⟩

/-- Section 4.2: "the order of τ is m - |Z|", for a leaf `τ` contributing to an output string `η`
with inner set `Q`. -/
theorem order_eq_sub_card_Zof (m : ℕ) (η : OutStr L) (τ : Leaf L)
    (hτ : Leaf.Contributes τ η) :
    order m τ = (m : ℤ) - ((Zof (innerSetO η) τ).card : ℤ) := by
  rw [order, P0Levels_eq_Zof η τ hτ]

/-- A leaf of order at least `t` contributing to `η` chooses `P₀` at most `m - t` times. -/
private lemma card_Zof_le {m t : ℕ} {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) : (Zof (innerSetO η) τ).card ≤ m - t := by
  have := order_eq_sub_card_Zof m η τ hτ
  omega

/-- `V` is a set of levels of `Q`. -/
theorem Vof_subset (m t : ℕ) {Q Z : Finset (Fin L)} (hZ : Z ⊆ Q) : Vof m t Q Z ⊆ Q :=
  union_subset hZ ((lowest_subset _ _).trans sdiff_subset)

/-- Section 4.2: "the set V has exactly m - t levels". -/
theorem card_Vof {m t : ℕ} (ht : t ≤ m) {Q Z : Finset (Fin L)} (hQ : Q.card = m) (hZ : Z ⊆ Q)
    (hZc : Z.card ≤ m - t) : (Vof m t Q Z).card = m - t := by
  have hdisj : Disjoint Z (lowest (m - t - Z.card) (Q \ Z)) :=
    disjoint_of_subset_right (lowest_subset _ _) disjoint_sdiff
  rw [Vof, card_union_of_disjoint hdisj, card_lowest, card_sdiff_of_subset hZ, hQ]
  -- `|Z| + min (m - t - |Z|) (m - |Z|) = m - t`, because `|Z| ≤ m - t ≤ m`
  omega

/-- `V` is `Z` "padded from the bottom" (Section 4.2): the levels added to `Z` are below the levels
of `Q` that are left out. -/
private lemma Vof_sdiff_lt (m t : ℕ) (Q Z : Finset (Fin L)) :
    ∀ ℓ ∈ Vof m t Q Z \ Z, ∀ ℓ' ∈ Q \ Vof m t Q Z, ℓ < ℓ' := by
  intro ℓ hℓ ℓ' hℓ'
  obtain ⟨hV, hZ⟩ := mem_sdiff.1 hℓ
  obtain ⟨hQ', hV'⟩ := mem_sdiff.1 hℓ'
  obtain ⟨hZ', hlow'⟩ := not_or.1 (mt mem_union.2 hV')
  -- `ℓ` is one of the lowest levels of `Q ∖ Z`, and `ℓ'` is another level of `Q ∖ Z`
  exact lowest_lt ((mem_union.1 hV).resolve_left hZ)
    (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hQ', hZ'⟩, hlow'⟩)








/-- Section 4.2: `F_V` "is the longest initial segment of Q contained in V". Here: it is contained
in `V`. -/
theorem FV_subset (Q V : Finset (Fin L)) : FV Q V ⊆ V := by
  intro ℓ hℓ
  by_contra hV
  exact lt_irrefl ℓ ((mem_filter.1 hℓ).2 ℓ (mem_sdiff.2 ⟨(mem_filter.1 hℓ).1, hV⟩))

/-- Section 4.2: `F_V` "is the longest initial segment of Q contained in V". Here: it is an initial
segment of `Q`. -/
private lemma mem_FV_of_le {Q V : Finset (Fin L)} {ℓ ℓ' : Fin L} (hℓ : ℓ ∈ FV Q V)
    (hℓ' : ℓ' ∈ Q) (hle : ℓ' ≤ ℓ) : ℓ' ∈ FV Q V :=
  mem_filter.2 ⟨hℓ', fun x hx => hle.trans_lt ((mem_filter.1 hℓ).2 x hx)⟩

/-- The core of the proof of Lemma 27: "V ∖ F_V ⊆ Z says that every level of V ∖ Z is below" the
lowest level, that is every level, of `Q ∖ V`. The paper's case `V = Q` needs no separate treatment:
then `Q ∖ V` is empty. -/
private lemma sdiff_FV_subset_iff {Q V Z : Finset (Fin L)} (hV : V ⊆ Q) :
    V \ FV Q V ⊆ Z ↔ ∀ ℓ ∈ V \ Z, ∀ ℓ' ∈ Q \ V, ℓ < ℓ' := by
  constructor
  · intro h ℓ hℓ ℓ' hℓ'
    obtain ⟨hℓV, hℓZ⟩ := mem_sdiff.1 hℓ
    have hℓF : ℓ ∈ FV Q V := by
      by_contra hF
      exact hℓZ (h (mem_sdiff.2 ⟨hℓV, hF⟩))
    exact (mem_filter.1 hℓF).2 ℓ' hℓ'
  · intro h ℓ hℓ
    obtain ⟨hℓV, hℓF⟩ := mem_sdiff.1 hℓ
    by_contra hZ
    exact hℓF (mem_filter.2 ⟨hV hℓV, h ℓ (mem_sdiff.2 ⟨hℓV, hZ⟩)⟩)

/-! ### The sets `𝓑_V` (Section 4.2) -/

section BV

variable {η : OutStr L} {V : Finset (Fin L)} {π : Cube L} {ℓ : Fin L}

/-- A cube of `𝓑_V` has a star at each level of `F_V`. -/
private lemma BV_star (hπ : π ∈ BV η V) (hℓ : ℓ ∈ FV (innerSetO η) V) : π ℓ = CubeSymbol.star :=
  ((mem_filter.1 hπ).2 ℓ).1 hℓ

/-- A cube of `𝓑_V` has `P₀` at each level of `V ∖ F_V`. -/
private lemma BV_P0 (hπ : π ∈ BV η V) (hℓ : ℓ ∈ V \ FV (innerSetO η) V) :
    π ℓ = CubeSymbol.term Term.P0 :=
  ((mem_filter.1 hπ).2 ℓ).2.1 hℓ

/-- A cube of `𝓑_V` has one of the nine terms `P_ij` at each level of `Q ∖ V`. -/
private lemma BV_nine (hπ : π ∈ BV η V) (hℓ : ℓ ∈ innerSetO η \ V) :
    ∃ i j, π ℓ = CubeSymbol.term (Term.P i j) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.1 hℓ

/-- A cube of `𝓑_V` has the term of the private leaf of `η` at each level outside `Q`. -/
private lemma BV_outside (hπ : π ∈ BV η V) (hℓ : ℓ ∉ innerSetO η) :
    π ℓ = CubeSymbol.term (privateLeaf η ℓ) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.2 hℓ

/-- Every level is of one of the four kinds in the definition of `𝓑_V`. -/
private lemma level_cases (Q V : Finset (Fin L)) (ℓ : Fin L) :
    ℓ ∈ FV Q V ∨ ℓ ∈ V \ FV Q V ∨ ℓ ∈ Q \ V ∨ ℓ ∉ Q := by
  simp only [mem_sdiff]
  tauto

/-- The stars of a cube of `𝓑_V` are at the levels of `F_V`. -/
theorem BV_starLevels (hπ : π ∈ BV η V) : Cube.starLevels π = FV (innerSetO η) V := by
  ext ℓ
  rw [Cube.mem_starLevels]
  refine ⟨fun h => ?_, BV_star hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · exact hℓ
  · simp [BV_P0 hπ hℓ] at h
  · obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
    simp [hij] at h
  · simp [BV_outside hπ hℓ] at h

/-- The symbols `P₀` of a cube of `𝓑_V` are at the levels of `V ∖ F_V`. -/
theorem BV_P0Levels (hπ : π ∈ BV η V) : Cube.P0Levels π = V \ FV (innerSetO η) V := by
  ext ℓ
  rw [Cube.mem_P0Levels]
  refine ⟨fun h => ?_, BV_P0 hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · simp [BV_star hπ hℓ] at h
  · exact hℓ
  · obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
    simp [hij] at h
  · rw [BV_outside hπ hℓ] at h
    exact absurd (CubeSymbol.term.inj h) (privateLeaf_ne_P0 hℓ)

/-- The levels at which a cube of `𝓑_V` has a star or `P₀` are those of `V`. -/
theorem BV_starLevels_union_P0Levels (hπ : π ∈ BV η V) :
    Cube.starLevels π ∪ Cube.P0Levels π = V := by
  rw [BV_starLevels hπ, BV_P0Levels hπ, union_sdiff_of_subset (FV_subset _ _)]

/-- Two cubes of `𝓑_V` with the same symbols at the levels of `Q ∖ V` are equal. -/
private lemma BV_ext {π' : Cube L} (hπ : π ∈ BV η V) (hπ' : π' ∈ BV η V)
    (h : ∀ ℓ ∈ innerSetO η \ V, π ℓ = π' ℓ) : π = π' := by
  funext ℓ
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · rw [BV_star hπ hℓ, BV_star hπ' hℓ]
  · rw [BV_P0 hπ hℓ, BV_P0 hπ' hℓ]
  · exact h ℓ hℓ
  · rw [BV_outside hπ hℓ, BV_outside hπ' hℓ]

/-- At a level of `Q ∖ V`, a cube of `𝓑_V` has the term of each of its leaves. -/
private lemma BV_eq_term_of_leaf (hπ : π ∈ BV η V) {τ : Leaf L} (hτ : τ ∈ Cube.leaves π)
    (hℓ : ℓ ∈ innerSetO η \ V) : π ℓ = CubeSymbol.term (τ ℓ) := by
  obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
  rw [hij, Cube.eq_of_mem_leaves hτ hij]

end BV









/-- `𝓑_V` is the set of all cubes with an allowed symbol at every level. -/
private lemma BV_eq_piFinset (η : OutStr L) (V : Finset (Fin L)) :
    BV η V = Fintype.piFinset (allowed η V) := by
  ext π
  simp [BV, allowed, Fintype.mem_piFinset]

/-- Nine symbols are allowed at a level of `Q ∖ V`, and one at every other level. -/
private lemma card_allowed (η : OutStr L) (V : Finset (Fin L)) (hV : V ⊆ innerSetO η)
    (ℓ : Fin L) : (allowed η V ℓ).card = if ℓ ∈ innerSetO η \ V then 9 else 1 := by
  have hnine :
      (univ.filter fun s : CubeSymbol => ∃ i j, s = CubeSymbol.term (Term.P i j)).card = 9 := by
    decide
  have hFV := @FV_subset L (innerSetO η) V ℓ
  have hVQ := @hV ℓ
  unfold allowed
  by_cases hF : ℓ ∈ FV (innerSetO η) V
  · simp [hF, hFV hF, hVQ (hFV hF), filter_eq']
  by_cases hℓV : ℓ ∈ V
  · simp [hF, hℓV, hVQ hℓV, filter_eq']
  by_cases hℓQ : ℓ ∈ innerSetO η
  · simp [hF, hℓV, hℓQ, hnine]
  · simp [hF, hℓV, hℓQ, filter_eq']

/-- Section 4.2: `𝓑_V` is "the set of the 9^t cubes π with" the symbols above. -/
theorem card_BV (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (V : Finset (Fin L)) (hV : V ∈ Vsets m t η) : (BV η V).card = 9 ^ t := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [BV_eq_piFinset η V, Fintype.card_piFinset]
  simp only [card_allowed η V hVQ]
  rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset hVQ, hη, hVc,
    Nat.sub_sub_self ht]

/-- Section 4.2: "Every cube in 𝓑_V is a box: it satisfies condition (i) of the definition because
it has |V| = m - t symbols P₀ or stars, and condition (ii) because its stars are below its symbols
P₀, since F_V is an initial segment of Q." -/
theorem BV_isBox {m t : ℕ} {η : OutStr L} {V : Finset (Fin L)} (hV : V ∈ Vsets m t η) {π : Cube L}
    (hπ : π ∈ BV η V) : IsBox m t π := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [IsBox, BV_starLevels hπ, BV_P0Levels hπ, add_comm,
    card_sdiff_add_card_eq_card (FV_subset _ _)]
  refine ⟨hVc.le, fun ℓ hℓ ℓ' hℓ' => ?_⟩
  -- otherwise `ℓ' ≤ ℓ` would be a level of the initial segment `F_V`
  obtain ⟨hℓ'V, hℓ'F⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hℓ'F (mem_FV_of_le hℓ (hVQ hℓ'V) (not_lt.1 hlt))

/-- The sets `𝓑_V` for different `V` are disjoint, so that the double sum `∑_V ∑_{π ∈ 𝓑_V}` of Lemma
28 runs over each box of `⋃_V 𝓑_V` once. -/
theorem BV_pairwiseDisjoint (η : OutStr L) (s : Set (Finset (Fin L))) :
    s.PairwiseDisjoint (BV η) :=
  -- a cube of `𝓑_V` determines `V`
  fun _ _ _ _ hne => disjoint_left.2 fun _ hπ hπ' =>
    hne ((BV_starLevels_union_P0Levels hπ).symm.trans (BV_starLevels_union_P0Levels hπ'))

/-- If `τ` contributes to `η` and `V ∖ F_V ⊆ Z ⊆ V`, then `τ` with stars at the levels of `F_V` is a
cube of `𝓑_V`. -/
private lemma starAt_mem_BV {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L}
    (hτ : Leaf.Contributes τ η) (hVZ : V \ FV (innerSetO η) V ⊆ Zof (innerSetO η) τ)
    (hZV : Zof (innerSetO η) τ ⊆ V) : Cube.starAt (FV (innerSetO η) V) τ ∈ BV η V := by
  refine mem_filter.2
    ⟨mem_univ _, fun ℓ => ⟨fun hF => if_pos hF, fun hVF => ?_, fun hQV => ?_, fun hQ => ?_⟩⟩
  · -- at a level of `V ∖ F_V`, which is a level of `Z`, the leaf chooses `P₀`
    rw [Cube.starAt, if_neg (mem_sdiff.1 hVF).2, (mem_filter.1 (hVZ hVF)).2]
  · -- at a level of `Q ∖ V`, which is not a level of `Z`, the leaf chooses another term
    obtain ⟨hQ, hV⟩ := mem_sdiff.1 hQV
    rw [Cube.starAt, if_neg fun hF => hV (FV_subset _ _ hF)]
    cases hterm : τ ℓ with
    | P i j => exact ⟨i, j, rfl⟩
    | P0 => exact absurd (hZV (mem_filter.2 ⟨hQ, hterm⟩)) hV
  · -- outside `Q` the leaf agrees with the private leaf
    rw [Cube.starAt, if_neg fun hF : ℓ ∈ FV (innerSetO η) V => hQ (mem_filter.1 hF).1,
      (contributes_iff_eq_privateLeaf η τ).1 hτ ℓ hQ]







/-- A leaf is a leaf of its box. -/
theorem mem_leaves_boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) :
    τ ∈ Cube.leaves (boxOfLeaf m t η τ) :=
  Cube.mem_leaves_starAt _ τ

/-- Section 4.2: "When V is the set defined above from a leaf τ, the box of τ is the one in 𝓑_V with
the terms of τ at the levels of Q ∖ V": it is a cube of `𝓑_V`, for the set `V` of `τ`. -/
theorem boxOfLeaf_mem_BV (m t : ℕ) {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    boxOfLeaf m t η τ ∈ BV η (Vof m t (innerSetO η) (Zof (innerSetO η) τ)) :=
  starAt_mem_BV hτ
    ((sdiff_FV_subset_iff (Vof_subset m t (Zof_subset _ τ))).2 (Vof_sdiff_lt m t _ _))
    subset_union_left

/-- Section 4.2: "A leaf contributing to w that chooses P₀ at the set Z of levels is a leaf of a box
of 𝓑_V if and only if it chooses P₀ at every level of V ∖ F_V and at no level of Q ∖ V, that is, V ∖
F_V ⊆ Z ⊆ V". -/
theorem exists_mem_BV_leaf_iff {η : OutStr L} {V : Finset (Fin L)} (hV : V ⊆ innerSetO η)
    {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    (∃ π ∈ BV η V, τ ∈ Cube.leaves π) ↔
      V \ FV (innerSetO η) V ⊆ Zof (innerSetO η) τ ∧ Zof (innerSetO η) τ ⊆ V := by
  constructor
  · rintro ⟨π, hπ, hτπ⟩
    refine ⟨fun ℓ hℓ => mem_filter.2 ⟨hV (mem_sdiff.1 hℓ).1, ?_⟩, fun ℓ hℓ => ?_⟩
    · exact Cube.eq_of_mem_leaves hτπ (BV_P0 hπ hℓ)
    · by_contra hℓV
      obtain ⟨hℓQ, hterm⟩ := mem_filter.1 hℓ
      obtain ⟨i, j, hij⟩ := BV_nine hπ (mem_sdiff.2 ⟨hℓQ, hℓV⟩)
      simp [Cube.eq_of_mem_leaves hτπ hij] at hterm
  · exact fun ⟨hVZ, hZV⟩ => ⟨_, starAt_mem_BV hτ hVZ hZV, Cube.mem_leaves_starAt _ τ⟩

/-- Section 4.2: "Furthermore, it is a leaf of exactly one of these boxes, namely, the one with its
terms at the levels of Q ∖ V." -/
theorem BV_leaf_unique {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L} {π π' : Cube L}
    (hπ : π ∈ BV η V) (hτπ : τ ∈ Cube.leaves π) (hπ' : π' ∈ BV η V) (hτπ' : τ ∈ Cube.leaves π') :
    π = π' :=
  BV_ext hπ hπ' fun _ hℓ =>
    (BV_eq_term_of_leaf hπ hτπ hℓ).trans (BV_eq_term_of_leaf hπ' hτπ' hℓ).symm

/-! ### Figure 10 -/
































/-! ### Lemma 27 -/

/-- **Lemma 27**. "Let Q be a set of m levels, and let 0 ≤ t ≤ m. For every Z ⊆ Q
with |Z| ≤ m - t, there is exactly one set V ⊆ Q with |V| = m - t and V ∖ F_V ⊆ Z ⊆ V, namely Z
together with the m - t - |Z| lowest levels of Q ∖ Z." This set is `Vof m t Q Z`. -/
theorem lemma_27 {L : ℕ} (m t : ℕ) (ht : t ≤ m) (Q Z : Finset (Fin L)) (hQ : Q.card = m)
    (hZ : Z ⊆ Q) (hZc : Z.card ≤ m - t) (V : Finset (Fin L)) :
    (V ⊆ Q ∧ V.card = m - t ∧ V \ FV Q V ⊆ Z ∧ Z ⊆ V) ↔ V = Vof m t Q Z := by
  constructor
  · rintro ⟨hVQ, hVc, hVZ, hZV⟩
    -- "Q ∖ Z is the disjoint union of V ∖ Z and Q ∖ V", and `V ∖ Z` lies below `Q ∖ V`,
    -- so "V ∖ Z consists of the lowest levels of Q ∖ Z".
    have hrest : (Q \ Z) \ (V \ Z) = Q \ V := sdiff_sdiff_sdiff_cancel_right hZV
    have hlow := eq_lowest_of_lt (sdiff_subset_sdiff hVQ (le_refl Z))
      (hrest ▸ (sdiff_FV_subset_iff hVQ).1 hVZ)
    rw [card_sdiff_of_subset hZV, hVc] at hlow
    rw [Vof, ← hlow, union_sdiff_of_subset hZV]
  · rintro rfl
    have hVQ := Vof_subset m t hZ
    exact ⟨hVQ, card_Vof ht hQ hZ hZc, (sdiff_FV_subset_iff hVQ).2 (Vof_sdiff_lt m t Q Z),
      subset_union_left⟩

/-! ### Lemma 28 -/

/-- **Lemma 28**, first sentence, first half. "Let w be an output string, with inner set
Q. The leaves of order at least t contributing to w are exactly the leaves of the boxes in ⋃_V 𝓑_V,
the union over all V ⊆ Q with |V| = m - t". -/
theorem lemma_28_leaves {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) :
    (Leaf.Contributes τ η ∧ (t : ℤ) ≤ order m τ) ↔
      ∃ π ∈ (Vsets m t η).biUnion (BV η), τ ∈ Cube.leaves π := by
  constructor
  · -- "Conversely, a leaf τ contributing to w, of order at least t," is a leaf of its box.
    rintro ⟨hτ, hord⟩
    refine ⟨boxOfLeaf m t η τ, mem_biUnion.2 ⟨_, mem_powersetCard.2 ?_, boxOfLeaf_mem_BV m t hτ⟩,
      mem_leaves_boxOfLeaf m t η τ⟩
    exact ⟨Vof_subset m t (Zof_subset _ τ),
      card_Vof ht hη (Zof_subset _ τ) (card_Zof_le hτ hord)⟩
  · -- "Every leaf of a box of 𝓑_V agrees with the private leaf of w outside Q, so it contributes
    -- to w", and a box only contains leaves of order at least `t`.
    rintro ⟨π, hπ, hτπ⟩
    obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
    exact ⟨(contributes_iff_eq_privateLeaf η τ).2 fun ℓ hℓ =>
        Cube.eq_of_mem_leaves hτπ (BV_outside hπV hℓ),
      le_order_of_mem_leaves ht (BV_isBox hV hπV) hτπ⟩

/-- Proof of Lemma 28: "By Lemma 27, exactly one V satisfies this condition": if a leaf of order at
least `t` contributing to `η` is a leaf of a box of `𝓑_V`, then `V` is the set of the leaf. -/
private lemma eq_Vof_of_mem_leaves {m t : ℕ} (ht : t ≤ m) {η : OutStr L}
    (hη : (innerSetO η).card = m) {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) {V : Finset (Fin L)} (hV : V ∈ Vsets m t η) {π : Cube L}
    (hπ : π ∈ BV η V) (hτπ : τ ∈ Cube.leaves π) :
    V = Vof m t (innerSetO η) (Zof (innerSetO η) τ) := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  obtain ⟨hVZ, hZV⟩ := (exists_mem_BV_leaf_iff hVQ hτ).1 ⟨π, hπ, hτπ⟩
  exact (lemma_27 m t ht _ _ hη (Zof_subset _ τ) (card_Zof_le hτ hord) V).1 ⟨hVQ, hVc, hVZ, hZV⟩

/-- **Lemma 28**, first sentence, second half: "and each of them is a leaf of exactly one
of these boxes." -/
theorem lemma_28_unique {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) (hτ : Leaf.Contributes τ η) (hord : (t : ℤ) ≤ order m τ) :
    ∃! π : Cube L, π ∈ (Vsets m t η).biUnion (BV η) ∧ τ ∈ Cube.leaves π := by
  obtain ⟨π, hπ, hτπ⟩ := (lemma_28_leaves m t ht η hη τ).1 ⟨hτ, hord⟩
  refine ⟨π, ⟨hπ, hτπ⟩, ?_⟩
  rintro π' ⟨hπ', hτπ'⟩
  -- the two boxes belong to the same `V`, and `𝓑_V` has only one box with the leaf `τ`
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  obtain ⟨V', hV', hπV'⟩ := mem_biUnion.1 hπ'
  obtain rfl : V' = V := (eq_Vof_of_mem_leaves ht hη hτ hord hV' hπV' hτπ').trans
    (eq_Vof_of_mem_leaves ht hη hτ hord hV hπV hτπ).symm
  exact BV_leaf_unique hπV' hτπ' hπV hτπ

/-- The equation of Lemma 28 for an arbitrary function `g` of the leaves in the place of the
products: the sum of `g` over the leaves contributing to `η` is the sum over the leaves of order
below `t` plus the sum over the leaves of the boxes. -/
theorem Lemma28.sum_contributing {G : Type*} [AddCommMonoid G] (m t : ℕ) (ht : t ≤ m)
    (η : OutStr L) (hη : (innerSetO η).card = m) (g : Leaf L → G) :
    ∑ τ : Leaf L with Leaf.Contributes τ η, g τ =
      ∑ τ ∈ lowLeaves m t η, g τ + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, ∑ τ ∈ Cube.leaves π, g τ := by
  have hdisjoint :
      (((Vsets m t η).biUnion (BV η) : Finset (Cube L)) : Set (Cube L)).PairwiseDisjoint
        Cube.leaves := by
    intro π hπ π' hπ' hne
    rw [Function.onFun, disjoint_left]
    intro τ hτ hτ'
    obtain ⟨hc, hord⟩ := (lemma_28_leaves m t ht η hη τ).2 ⟨π, hπ, hτ⟩
    exact hne ((lemma_28_unique m t ht η hη τ hc hord).unique ⟨hπ, hτ⟩ ⟨hπ', hτ'⟩)
  have hhigh : ((Vsets m t η).biUnion (BV η)).biUnion Cube.leaves =
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ ¬ order m τ < (t : ℤ) := by
    ext τ
    rw [mem_biUnion, mem_filter, not_lt, ← lemma_28_leaves m t ht η hη τ]
    simp
  -- The sums over the sets `V`, the boxes and their leaves are one sum over the contributing leaves
  -- of order at least `t`; the contributing leaves split into those of order below `t` and these.
  rw [← sum_biUnion (BV_pairwiseDisjoint η _), ← sum_biUnion hdisjoint, hhigh, lowLeaves,
    ← filter_filter, ← filter_filter, sum_filter_add_sum_filter_not]

/-- **Lemma 28**, the displayed equation, for arbitrary input arrays: the sum of the products at the
leaves contributing to `η`, which is `Mult(a, b)[η]`, equals the sum over the leaves of order below
`t` plus the sum of the values of the boxes. See `lemma_28` for the form with `(X_Q Y_Q)[η]` on the
left. -/
theorem Lemma28.Mult_eq_querySum (m t : ℕ) (ht : t ≤ m) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (η : OutStr L) (hη : (innerSetO η).card = m) : Mult a b η = querySum m t a b η :=
  Lemma28.sum_contributing m t ht η hη fun τ => Phi τ a * Psi τ b










/-- The terms of the sum of Lemma 28 stand for the `10^m` leaves contributing to `η`, each of them
once: one leaf for each product, and its leaves for each box. The bound on the partial sums of a
query (word size, the proof of Theorem 30) rests on this count. -/
theorem Lemma28.card_leaves (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card + ∑ π ∈ (Vsets m t η).biUnion (BV η), (Cube.leaves π).card = 10 ^ m := by
  have hsplit := Lemma28.sum_contributing m t ht η hη fun _ => 1
  rw [← card_eq_sum_ones, card_filter_contributes η hη] at hsplit
  rw [hsplit, sum_biUnion (BV_pairwiseDisjoint η _)]
  simp

/-- The leaves of order below `t` contributing to `η`, sorted by their order, which is at least 0.
-/
private lemma lowLeaves_eq_biUnion (m t : ℕ) (η : OutStr L) (hη : (innerSetO η).card = m) :
    lowLeaves m t η = (range t).biUnion fun d =>
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ order m τ = d := by
  ext τ
  simp only [lowLeaves, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
  constructor
  · rintro ⟨hτ, hlt⟩
    have hnonneg := order_nonneg hη hτ
    exact ⟨(order m τ).toNat, by omega, hτ, (Int.toNat_of_nonneg hnonneg).symm⟩
  · rintro ⟨d, hd, hτ, heq⟩
    exact ⟨hτ, by omega⟩

/-- **Lemma 28**, last line: "a sum of ∑_{d=0}^{t-1} α_d products and α_t values of
boxes."  The third clause says that these α_t cubes are different, that is, that the sets 𝓑_V are
disjoint; Section 4.2 has it in the words "w has exactly α_t boxes". -/
theorem lemma_28_counts {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card = ∑ d ∈ range t, alpha m d ∧
      ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t ∧
      ((Vsets m t η).biUnion (BV η)).card = alpha m t := by
  -- "there are binom(m, m-t) sets V with 9^t boxes each"
  have hsum : ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t := by
    rw [sum_congr rfl fun V hV => card_BV m t ht η hη V hV, sum_const, Vsets,
      card_powersetCard, hη, Nat.choose_symm ht, smul_eq_mul, alpha]
  refine ⟨?_, hsum, ?_⟩
  · -- "α_d leaves of order d contribute to w"
    rw [lowLeaves_eq_biUnion m t η hη, card_biUnion]
    · exact sum_congr rfl fun d _ => sec2_card_contributing_of_order η hη d
    · intro d _ d' _ hne
      rw [Function.onFun, disjoint_left]
      intro τ hd hd'
      exact hne (by exact_mod_cast (mem_filter.1 hd).2.2.symm.trans (mem_filter.1 hd').2.2)
  · rw [card_biUnion (BV_pairwiseDisjoint η _), hsum]










end ThreeSumApsp

end
end

section


/-!
# The boxes of an output string, from its leaves of order exactly `t` (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. The boxes of `η` are
the cubes of the sets `𝓑_V`, over all `V ⊆ Q` with `|V| = m - t`. This file proves two passages of
the running text of Section 4.2 about them.

* *Every box of `η` has exactly `m - t` symbols that are `P₀` or stars*
  (`card_starLevels_add_card_P0Levels`).
* *The second description.* Take a leaf of order exactly `t` contributing to `η` and replace its
  `P₀` by a star at every level of `Q` below the lowest level of `Q` at which it chooses another
  term, or at every level of `Q` if `t = 0` (`starBelow`). For such a leaf this is the box of the
  leaf (`boxOfLeaf_eq_starBelow`), so it is a box of `η` (`starBelow_mem`). Replacing the stars with
  `P₀` gives the leaf back (`starsToP0_starBelow`), and it turns every box of `η` into a leaf of
  order exactly `t` contributing to `η` (`starsToP0_of_mem`). So each box of `η` arises exactly once
  (`existsUnique_starBelow_eq`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m t : ℕ} {η : OutStr L} {τ : Leaf L}
















/-- A leaf of order exactly `t` contributing to `η` chooses `P₀` at exactly `m - t` levels. -/
private lemma card_Zof_eq (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    (Zof (innerSetO η) τ).card = m - t := by
  have := order_eq_sub_card_Zof m η τ hτ
  omega

/-- A set `Z` of `m - t` levels needs no padding: `V = Z`. -/
private lemma Vof_eq_self (Q Z : Finset (Fin L)) (hZ : Z.card = m - t) : Vof m t Q Z = Z := by
  simp [Vof, lowest, hZ]

/-- For a leaf of order exactly `t` contributing to `η`, the cube of the second description is the
box of the leaf. -/
theorem boxOfLeaf_eq_starBelow (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    boxOfLeaf m t η τ = starBelow η τ := by
  rw [boxOfLeaf, starBelow, Vof_eq_self _ _ (card_Zof_eq hτ hord)]





/-- Section 4.2: "The result is a box of w". -/
theorem starBelow_mem (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    starBelow η τ ∈ (Vsets m t η).biUnion (BV η) := by
  have hmem := boxOfLeaf_mem_BV m t hτ
  rw [boxOfLeaf_eq_starBelow hτ hord, Vof_eq_self _ _ (card_Zof_eq hτ hord)] at hmem
  exact mem_biUnion.2 ⟨_, mem_powersetCard.2 ⟨filter_subset _ _, card_Zof_eq hτ hord⟩, hmem⟩




























end ThreeSumApsp

end
end

section


/-!
# Lemma 29: the number of boxes, and their values (Section 4.3)

*The count* (`lemma_29_count`): there are at most `(m+1) ∑_{d=t}^{m} β_d` boxes. A box with `f`
symbols `P₀` or stars is a leaf with `f` symbols `P₀` in which the `e` lowest of them have been
turned into stars, for some `e ≤ f`. So these boxes correspond to the pairs of such a leaf and a
number `e ≤ f`, there are `(f+1) β_{m-f}` of them (`Lemma29.card_filter`), and we sum over
`f ≤ m - t`.

*The values* (`lemma_29_values`): the dynamic program `dpValue`, run on the two encodings of a tile,
returns the value of every box. This is an induction on the number of stars. The boxes without stars
are leaves (`Lemma29.no_stars`), and their values are products of two encoded numbers
(`Lemma29.val_ofLeaf`). Replacing the highest star of a box by the ten terms gives ten boxes with
one star fewer (`lemma_29_split`), whose values add up to the value of the box
(`Lemma29.recurrence`).
-/

public section

open Finset

namespace ThreeSumApsp

/-- Membership in the set of all boxes. -/
@[simp]
theorem mem_boxes {L m t : ℕ} {π : Cube L} : π ∈ boxes L m t ↔ IsBox m t π := by
  simp [boxes]

/-- Membership in the set of the boxes with `e` stars. -/
@[simp]
theorem mem_boxesWithStars {L m t e : ℕ} {π : Cube L} :
    π ∈ boxesWithStars L m t e ↔ IsBox m t π ∧ (Cube.starLevels π).card = e := by
  simp [boxesWithStars, boxes]

/-! ### The count -/







































































/-! ### The values -/

/-- Proof of Lemma 29, "The values": "The boxes without stars are the leaves with at most m - t
symbols P₀". -/
theorem Lemma29.no_stars {L : ℕ} (m t : ℕ) (π : Cube L) :
    π ∈ boxesWithStars L m t 0 ↔ ∃ τ : Leaf L, (P0Levels τ).card ≤ m - t ∧ π = Cube.ofLeaf τ := by
  rw [mem_boxesWithStars]
  constructor
  · rintro ⟨hbox, hstar⟩
    refine ⟨Cube.starsToP0 π, ?_,
      Cube.eq_ofLeaf_of_starLevels_eq_empty π (card_eq_zero.1 hstar)⟩
    rw [card_P0Levels_starsToP0]
    exact hbox.1
  · rintro ⟨τ, hτ, rfl⟩
    rw [IsBox, Cube.starLevels_ofLeaf, Cube.P0Levels_ofLeaf]
    simpa using hτ

/-- Proof of Lemma 29, "The values": "the value of each of them is the product of its two numbers in
the encodings." -/
theorem Lemma29.val_ofLeaf {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) :
    Cube.val a b (Cube.ofLeaf τ) = Phi τ a * Psi τ b := by
  rw [Cube.val, Cube.leaves_ofLeaf, sum_singleton, productAt]






















/-- Proof of Lemma 29, "The values", the displayed recurrence: "val(π) = ∑_λ val(π[ℓ ← λ])", because
"The leaves of π are the leaves of the ten strings π[ℓ ← λ]". It holds for a star at any level `ℓ`
of any cube `π`. -/
theorem Lemma29.recurrence {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (ℓ : Fin L) (hℓ : π ℓ = CubeSymbol.star) :
    Cube.val a b π = ∑ lam : Term, Cube.val a b (Cube.replace π ℓ lam) := by
  unfold Cube.val
  rw [← sum_fiberwise (Cube.leaves π) (fun τ => τ ℓ)]
  refine sum_congr rfl fun lam _ => sum_congr ?_ fun _ _ => rfl
  ext τ
  rw [mem_filter, Cube.mem_leaves_replace hℓ]

/-- **Lemma 29**, second sentence, correctness: "Given the two encodings of a tile, we can compute
the values of all these boxes". The recurrence of the dynamic program of the proof (`dpValue`), run
on the two encodings, returns `val(π)` for every box `π` with `e` stars. That the ten strings π[ℓ ←
λ] are boxes with `e - 1` stars, so that their values can be looked up, is `lemma_29_split`. (For
the time and space bound see `docs/REMARKS.md`, "Section 4: running times".) -/
theorem lemma_29_values (L m t e : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (hπ : π ∈ boxesWithStars L m t e) :
    dpValue (encodingL a) (encodingR b) e π = Cube.val a b π := by
  induction e generalizing π with
  | zero =>
    obtain ⟨τ, -, rfl⟩ := (Lemma29.no_stars m t π).1 hπ
    rw [Lemma29.val_ofLeaf]
    -- by definition, the leaf of the cube `Cube.ofLeaf τ` is `τ`, and the encodings hold `Φ_τ(a)`
    -- and `Ψ_τ(b)`
    rfl
  | succ e ih =>
    have hne : (Cube.starLevels π).Nonempty :=
      card_pos.1 ((mem_boxesWithStars.1 hπ).2 ▸ Nat.succ_pos e)
    rw [dpValue, dif_pos hne,
      Lemma29.recurrence a b π _ (Cube.mem_starLevels.1 (max'_mem _ hne))]
    exact sum_congr rfl fun lam _ => ih _ (lemma_29_split hπ hne lam)

end ThreeSumApsp

end
end

section


/-!
# Equation (7) and Theorem 30: the data structure (Section 4.3)

The running times of Theorem 30 on the word RAM are `wordRam_theorem_30` and
`wordRam_theorem_30_wanted`; the expressions inside their `O(·)` are `cost8`, `cost9` and
`costQuery`. This file has the mathematics of the paper's proof, in the paper's order.

* *The decay rate.* `ρ = 9m/(L-m+1)` is less than 1 (`sec4_rho_lt_one`), the ratio `β_d/β_{d-1}` is
  at most `ρ` (`eq_7_ratio`), and so `β_d ≤ ρ^d M` (`eq_7`). This is equation (7).
* *Preprocessing: the count behind (8).* Here `sqrtKN0 L m` is `√K N₀`. Padding at most doubles `N`
  (`Theorem30.padding`; nothing else rests on this lemma). The list of subsets takes `K L ≤ 10^L`
  operations (`Theorem30.subsets`), which the last term of (8) absorbs
  (`Theorem30.subsets_absorbed`). There are at most `4N/(√K N₀)` bands (`Theorem30.bands`), with `N`
  the given size, by a slightly finer count than `K₀ ≥ √K/2` gives (`Theorem30.numBands_mul_le`);
  the input array of a band has at most `K N₀ D ≤ 7^L` nonzero entries
  (`Theorem30.K_mul_N0_mul_D_le`), and `L · 7^L ≤ 2 · 10^L` (`Theorem30.form_array`). There are at
  most `4N²/M` tiles (`Theorem30.tiles`) with at most `(m+1) ∑_{d ≥ t} β_d` boxes each (Lemma 29),
  and `∑_{d ≥ t} β_d ≤ M ρ^t/(1-ρ)` by (7) (`Theorem30.sum_beta`), which bounds the number of all
  boxes (`Theorem30.boxes_total`). The boxes (`Theorem30.boxes_cost`), the bands
  (`Theorem30.bands_cost`) and the list add up to at most a constant times the expression in (8)
  (`Theorem30.cost8_assembly`).
* *Query.* The sum of Lemma 28 for the output string of the position `(I, J)` is `(XY)[I, J]` by
  Section 2.4.4 (`Theorem30.query`). Each box of that sum is a box of the tile (`Theorem30.lookup`),
  and the dynamic program of Lemma 29 has stored its value (`dpValue_card_starLevels`); so the query
  returns `(XY)[I, J]` (`Theorem30.correct`). Expression (9) is `|W|` queries on top of (8)
  (`Theorem30.cost9_eq`).
* *Word size.* `10^L ≤ N^{5/2}` (`Theorem30.ten_pow_le`).

Here `N` is the given size throughout, and the padded size is `padN L m N`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### The decay rate `ρ` and equation (7) -/




















































/-! ### Theorem 30, "Preprocessing": the count behind (8) -/










































































































































































































































/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/

/-- Proof of Theorem 30, "Query". "Given (I, J), we find its tile from the bands of row I and column
J, the subset Q of its block product, and its output string w […]. We then compute (X_Q Y_Q)[w] as
the sum in Lemma 28 […]. By Section 2.4.4, the sum is (XY)[I, J]." Here `a` and `b` are the input
arrays of the row band of `I` and of the column band of `J`, and `lay` is any choice of the indexing
bijections and of the subsets of the block products; it carries `m ≤ L`. (The hypotheses `m ≥ 1`,
`L ≥ 10m` and `N ≥ √K N₀` of Theorem 30 are not needed for correctness.) -/
theorem Theorem30.query {L m N : ℕ} (t : ℕ) (ht : t ≤ m) (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    querySum m t (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J))
        (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma28.Mult_eq_querySum m t ht _ _ _ (card_innerSetO_outStrOfPos lay I J)]
  exact Mult_bandArray_eq_mul lay X Y I J

/-- Proof of Theorem 30, "Query": "for every V ⊆ Q with |V| = m - t and every box of 𝓑_V, we look up
its value in the trie of the tile." It is there: it is a box. -/
theorem Theorem30.lookup {L m t : ℕ} {η : OutStr L} {V : Finset (Fin L)} (hV : V ∈ Vsets m t η)
    {π : Cube L} (hπ : π ∈ BV η V) : π ∈ boxes L m t :=
  mem_boxes.2 (BV_isBox hV hπ)

/-- What the dynamic program of Lemma 29 computes for a box, at the number of stars of the box, is
the value of the box. -/
theorem dpValue_card_starLevels {L m t : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) {π : Cube L}
    (hπ : π ∈ boxes L m t) :
    dpValue (encodingL a) (encodingR b) (Cube.starLevels π).card π = Cube.val a b π :=
  lemma_29_values L m t _ a b π
    (mem_boxesWithStars.2 ⟨mem_boxes.1 hπ, rfl⟩)











/-- **Theorem 30**, correctness of the data structure from end to end: the preprocessing computes
the encodings of the bands and, from them, the values of the boxes of every tile by the dynamic
program of Lemma 29; a query for `(I, J)` reads only the two encodings of its tile and the stored
values of boxes, and returns `(XY)[I, J]`. -/
theorem Theorem30.correct {L m N : ℕ} (t : ℕ) (ht : t ≤ m) (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    queryValue m t (encodingL (bandArrayL lay X (bandOf L m I)))
        (encodingR (bandArrayR lay Y (bandOf L m J))) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Theorem30.query t ht lay X Y I J]
  unfold queryValue querySum
  -- the products at the leaves are read from the encodings, by definition; the stored values of the
  -- boxes are their values, by Lemma 29
  congr 1
  exact sum_congr rfl fun V hV => sum_congr rfl fun π hπ =>
    dpValue_card_starLevels _ _ (Theorem30.lookup hV hπ)







/-! ### Theorem 30, "Word size" -/















end ThreeSumApsp

end
end

section


/-!
# Cubes, leaves and output strings as lists of digits (Sections 4.2 and 4.3)

A term has the digit P_ij ↦ 3(i - 1) + (j - 1), P₀ ↦ 9, and an output variable the digit
z_ij ↦ 3(i - 1) + (j - 1), z₀ ↦ 9.  A symbol of a cube that is a term keeps the digit of the term,
and the star has the digit 10.  A cube, a leaf or an output string is handled as the list of its L
digits, level 1 first: `digitsC` for cubes, `digitsT` for strings of terms (leaves), `digitsO` for
output strings.  This file translates the notions of Sections 4.2 and 4.3 into operations on such
lists:

* the inner set of an output string η (the paper's w) is the positions of its digit 9, the stars of
  π are the positions of 10, the symbols P₀ of τ the positions of 9, and their numbers are counts
  (`card_innerSetO`, `card_starLevels`, `card_P0Levels`);
* "replacing its e lowest symbols P₀ […] by stars" is `starFirst` (`digitsC_starLowest`);
* "replacing its stars with P₀" is `starsToNines` (`digitsT_starsToP0`);
* "the highest level at which π has a star" is `lastStar` (`lastStar_digitsC`), and π[ℓ ← λ] is
  `List.set` (`digitsC_replace`);
* the dynamic program of Lemma 29 is `dpValueD` (`dpValueD_digitsC`): the product `leafProduct` for
  a list without stars, and the step `sumAtLastStar`; `storedD` is what it computes for a box, at
  the number of stars of the box.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Cubes, leaves and output strings -/

































section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)

theorem length_digitsC : (digitsC π).length = L := length_digitsStr _ π
theorem length_digitsT : (digitsT τ).length = L := length_digitsStr _ τ
theorem length_digitsO : (digitsO η).length = L := length_digitsStr _ η

theorem digitsC_lt : ∀ d ∈ digitsC π, d < 11 := digitsStr_lt _ π
theorem digitsT_lt : ∀ d ∈ digitsT τ, d < 10 := digitsStr_lt _ τ
theorem digitsO_lt : ∀ d ∈ digitsO η, d < 10 := digitsStr_lt _ η

private theorem getD_digitsC (ℓ : Fin L) : (digitsC π).getD ℓ 0 = cubeIdx (π ℓ) :=
  getD_digitsStr _ π ℓ
theorem getD_digitsT (ℓ : Fin L) : (digitsT τ).getD ℓ 0 = termIdx (τ ℓ) := getD_digitsStr _ τ ℓ
theorem getD_digitsO (ℓ : Fin L) : (digitsO η).getD ℓ 0 = outIdx (η ℓ) := getD_digitsStr _ η ℓ

/-- A list with L members and the right digit at every level is the list of digits of the cube. -/
theorem digitsC_eq_of_getD {l : List ℕ} (hl : l.length = L)
    (h : ∀ ℓ : Fin L, l.getD ℓ 0 = cubeIdx (π ℓ)) : digitsC π = l :=
  digitsStr_eq_of_getD cubeEquiv π hl h

theorem ofDigitList_digitsT : ofDigitList 10 (digitsT τ) = codeT τ := ofDigitList_digitsStr _ τ
theorem ofDigitList_digitsO : ofDigitList 10 (digitsO η) = codeO η := ofDigitList_digitsStr _ η

end

theorem digitsC_injective (L : ℕ) : Function.Injective (digitsC : Cube L → List ℕ) :=
  digitsStr_injective _
theorem digitsT_injective (L : ℕ) : Function.Injective (digitsT : Leaf L → List ℕ) :=
  digitsStr_injective _

/-- Every list of L digits below 10 is the list of digits of a leaf. -/
theorem exists_digitsT {L : ℕ} (l : List ℕ) (hl : l.length = L) (hd : ∀ d ∈ l, d < 10) :
    ∃ τ : Leaf L, digitsT τ = l := exists_digitsStr _ l hl hd

/-! ## The levels of a symbol are the positions of its digit -/




private theorem cubeIdx_star : (cubeIdx .star : ℕ) = 10 := rfl

theorem cubeIdx_term (lam : Term) : (cubeIdx (.term lam) : ℕ) = termIdx lam := rfl

/-- The star is the only symbol with the digit 10. -/
private theorem cubeIdx_eq_ten (s : CubeSymbol) : (cubeIdx s : ℕ) = 10 ↔ s = .star := by
  cases s with
  | term lam =>
    have := (termIdx lam).isLt
    simp only [cubeIdx, reduceCtorEq, iff_false]
    omega
  | star => simp [cubeIdx]

/-- P₀ is the only term with the digit 9. -/
theorem termIdx_eq_nine (lam : Term) : (termIdx lam : ℕ) = 9 ↔ lam = .P0 := by
  cases lam with
  | P i j =>
    simp only [termIdx, reduceCtorEq, iff_false]
    omega
  | P0 => simp [termIdx]

section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)

/-- The levels of the inner set are the positions of the digit 9. -/
theorem getD_digitsO_eq_nine (ℓ : Fin L) : (digitsO η).getD ℓ 0 = 9 ↔ ℓ ∈ innerSetO η := by
  rw [getD_digitsO, innerSetO, Finset.mem_filter_univ, outVar_isInner_iff]

/-- A statement on all positions of the digit 9 is a statement on all levels of the inner set. -/
theorem forall_nine_digitsO (P : ℕ → Prop) :
    (∀ j, (digitsO η).getD j 0 = 9 → P j) ↔ ∀ ℓ ∈ innerSetO η, P ℓ :=
  (forall_getD_digitsStr outEquiv η (by norm_num) P).trans <| forall_congr' fun ℓ => by
    rw [← getD_digitsO_eq_nine, getD_digitsO]
    rfl

/-- A statement on all positions of the digit 10 is a statement on all levels with a star. -/
private theorem forall_ten_digitsC (P : ℕ → Prop) :
    (∀ j, (digitsC π).getD j 0 = 10 → P j) ↔ ∀ ℓ ∈ Cube.starLevels π, P ℓ :=
  (forall_getD_digitsStr cubeEquiv π (by norm_num) P).trans <| forall_congr' fun ℓ => by
    rw [Cube.starLevels, Finset.mem_filter_univ, ← cubeIdx_eq_ten]
    rfl

/-- The size of the inner set is the number of digits 9. -/
theorem card_innerSetO : (innerSetO η).card = (digitsO η).count 9 := by
  rw [digitsO, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => outVar_isInner_iff (η ℓ))

/-- The number of stars is the number of digits 10. -/
theorem card_starLevels : (Cube.starLevels π).card = starCount (digitsC π) := by
  rw [starCount, digitsC, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => (cubeIdx_eq_ten (π ℓ)).symm)

/-- The number of symbols P₀ is the number of digits 9. -/
theorem card_P0Levels : (P0Levels τ).card = (digitsT τ).count 9 := by
  rw [digitsT, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => (termIdx_eq_nine (τ ℓ)).symm)

end

/-! ## The lowest symbols P₀ turned into stars -/











theorem length_starFirst (e : ℕ) (l : List ℕ) : (starFirst e l).length = l.length := by
  fun_induction starFirst e l <;> simp_all

/-- The digits of `starFirst e l`: a digit 9 with fewer than e digits 9 before it becomes 10. -/
theorem getD_starFirst (e : ℕ) (l : List ℕ) (i : ℕ) :
    (starFirst e l).getD i 0
      = if l.getD i 0 = 9 ∧ (l.take i).count 9 < e then 10 else l.getD i 0 := by
  fun_induction starFirst e l generalizing i <;> cases i <;> simp_all

/-- Replacing the e lowest symbols P₀ of a leaf by stars is `starFirst e` on its digits. -/
theorem digitsC_starLowest {L : ℕ} (e : ℕ) (τ : Leaf L) :
    digitsC (starLowest e τ) = starFirst e (digitsT τ) := by
  refine digitsC_eq_of_getD _ (by rw [length_starFirst, length_digitsT]) fun ℓ => ?_
  have hcount : ((digitsT τ).take ℓ).count 9 = ((P0Levels τ).filter fun ℓ' => ℓ' < ℓ).card := by
    rw [digitsT, digitsStr, List.count_take_ofFn]
    refine congrArg Finset.card (Finset.ext fun ℓ' => ?_)
    rw [Finset.mem_filter_univ, Finset.mem_filter, P0Levels, Finset.mem_filter_univ, Fin.lt_def,
      and_comm]
    exact and_congr_left' (termIdx_eq_nine (τ ℓ'))
  have hmem : ℓ ∈ lowest e (P0Levels τ) ↔
      (digitsT τ).getD ℓ 0 = 9 ∧ ((digitsT τ).take ℓ).count 9 < e := by
    rw [hcount, getD_digitsT, termIdx_eq_nine, lowest, Finset.mem_filter, P0Levels,
      Finset.mem_filter_univ]
  rw [getD_starFirst, starLowest, Cube.starAt]
  by_cases hc : ℓ ∈ lowest e (P0Levels τ)
  · rw [if_pos hc, if_pos (hmem.mp hc), cubeIdx_star]
  · rw [if_neg hc, if_neg fun h => hc (hmem.mpr h), getD_digitsT, cubeIdx_term]

/-! ## Stars turned into P₀, and a symbol replaced by a term -/




/-- A list without the digit 10 is not changed. -/
theorem starsToNines_of_notMem {s : List ℕ} (h : 10 ∉ s) : starsToNines s = s := by
  rw [starsToNines]
  conv_rhs => rw [← List.map_id s]
  exact List.map_congr_left fun d hd => if_neg fun h' : d = 10 => h (h' ▸ hd)

/-- Turning the stars back into nines undoes `starFirst`. -/
theorem starsToNines_starFirst (e : ℕ) {l : List ℕ} (h : 10 ∉ l) :
    starsToNines (starFirst e l) = l := by
  fun_induction starFirst e l with
  | case1 l => exact starsToNines_of_notMem h
  | case2 => rfl
  | case3 e l ih => simp_all [starsToNines]
  | case4 e d l hd ih =>
    rw [starsToNines, List.map_cons, if_neg fun h10 : d = 10 => h (h10 ▸ List.mem_cons_self)]
    exact congrArg (d :: ·) (ih fun h' => h (List.mem_cons_of_mem _ h'))

/-- Replacing the stars of a cube with P₀ is `starsToNines` on its digits. -/
private theorem digitsT_starsToP0 {L : ℕ} (π : Cube L) :
    digitsT (Cube.starsToP0 π) = starsToNines (digitsC π) := by
  rw [digitsT, starsToNines, digitsC, digitsStr, digitsStr, List.map_ofFn]
  refine congrArg List.ofFn (funext fun ℓ => ?_)
  simp only [Cube.starsToP0, Function.comp]
  cases π ℓ with
  | term lam => exact (if_neg (Nat.ne_of_lt (termIdx lam).isLt)).symm
  | star => rfl

/-- π[ℓ ← λ] (the proof of Lemma 29) on digits: the digit at position ℓ is set to the digit of λ. -/
theorem digitsC_replace {L : ℕ} (π : Cube L) (ℓ : Fin L) (lam : Term) :
    digitsC (Cube.replace π ℓ lam) = (digitsC π).set ℓ (termIdx lam) := by
  refine digitsC_eq_of_getD _ (by rw [List.length_set, length_digitsC]) fun i => ?_
  rw [Cube.replace, List.getD_eq_getElem?_getD]
  by_cases h : i = ℓ
  · rw [h, Function.update_self, List.getElem?_set_self (by rw [length_digitsC]; exact ℓ.isLt),
      cubeIdx_term, Option.getD_some]
  · rw [Function.update_of_ne h, List.getElem?_set_ne fun hℓi => h (Fin.ext hℓi.symm),
      ← List.getD_eq_getElem?_getD, getD_digitsC]

/-! ## The highest star -/










/-- `lastStar` finds nothing exactly if the digit 10 does not occur. -/
private theorem lastStar_eq_none_iff (l : List ℕ) : lastStar l = none ↔ ∀ j, l.getD j 0 ≠ 10 := by
  induction l with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [← Nat.and_forall_add_one, lastStar]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ← ih]
    cases lastStar l <;> simp

/-- `lastStar` finds the last position of the digit 10. -/
theorem lastStar_eq_some_iff (l : List ℕ) (p : ℕ) :
    lastStar l = some p ↔ l.getD p 0 = 10 ∧ ∀ j, p < j → l.getD j 0 ≠ 10 := by
  induction l generalizing p with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [← Nat.and_forall_add_one, lastStar]
    cases p with
    | zero =>
      simp only [List.getD_cons_zero, List.getD_cons_succ, lt_irrefl, false_imp_iff, true_and,
        Nat.zero_lt_succ, forall_true_left, ← lastStar_eq_none_iff]
      cases lastStar l <;> simp
    | succ p =>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.not_lt_zero, false_imp_iff,
        true_and, Nat.add_lt_add_iff_right, ← ih]
      cases lastStar l <;> simp

/-- On the digits of a cube with a star, `lastStar` finds the highest level at which it has a
star. -/
theorem lastStar_digitsC {L : ℕ} (π : Cube L) (h : (Cube.starLevels π).Nonempty) :
    lastStar (digitsC π) = some ((Cube.starLevels π).max' h : ℕ) := by
  have hmax := (forall_ten_digitsC π fun j => ¬ ((Cube.starLevels π).max' h : ℕ) < j).mpr
    fun ℓ hℓ => not_lt.mpr (Fin.le_def.mp (Finset.le_max' _ _ hℓ))
  refine (lastStar_eq_some_iff _ _).mpr ⟨?_, fun j hj h10 => hmax j h10 hj⟩
  rw [getD_digitsC, cubeIdx_eq_ten]
  simpa [Cube.starLevels] using Finset.max'_mem _ h

/-- `lastStar` finds nothing exactly if the cube has no star. -/
private theorem lastStar_digitsC_eq_none_iff {L : ℕ} (π : Cube L) :
    lastStar (digitsC π) = none ↔ Cube.starLevels π = ∅ := by
  rw [lastStar_eq_none_iff, Finset.eq_empty_iff_forall_notMem]
  exact forall_ten_digitsC π fun _ => False

/-! ## The dynamic program of Lemma 29 on digits -/


















/-- The step of the dynamic program uses only the ten values that it adds up. -/
theorem sumAtLastStar_congr {val val' : List ℕ → ℤ} {l : List ℕ} {p : ℕ} (hp : lastStar l = some p)
    (h : ∀ d < 10, val (l.set p d) = val' (l.set p d)) :
    sumAtLastStar val l = sumAtLastStar val' l := by
  rw [sumAtLastStar, sumAtLastStar, hp]
  exact congrArg List.sum (List.map_congr_left fun d hd => h d (List.mem_range.mp hd))










/-- On the arrays of two encodings, the product at the digits of a leaf is the product of its two
numbers. -/
theorem leafProduct_digitsT {L : ℕ} (encA encB : Leaf L → ℤ) (τ : Leaf L) :
    leafProduct (arrT encA) (arrT encB) (digitsT τ) = encA τ * encB τ := by
  rw [leafProduct, ofDigitList_digitsT, getD_arrT, getD_arrT]

/-- The dynamic program on digits, run on the arrays of the two encodings, is the dynamic program
of Lemma 29. -/
theorem dpValueD_digitsC {L : ℕ} (encA encB : Leaf L → ℤ) (e : ℕ) (π : Cube L) :
    dpValueD (arrT encA) (arrT encB) e (digitsC π) = dpValue encA encB e π := by
  induction e generalizing π with
  | zero => rw [dpValueD, dpValue, ← digitsT_starsToP0, leafProduct_digitsT]
  | succ e ih =>
    rw [dpValueD, dpValue, sumAtLastStar]
    by_cases h : (Cube.starLevels π).Nonempty
    · rw [dif_pos h, lastStar_digitsC π h]
      -- a star is found: the sum of ten values
      simp only [tenValues]
      rw [List.sum_map_range, ← Fin.sum_univ_eq_sum_range, ← termEquiv.sum_comp]
      refine Finset.sum_congr rfl fun lam _ => ?_
      rw [← ih, digitsC_replace]
      rfl
    · rw [dif_neg h, (lastStar_digitsC_eq_none_iff π).mpr (Finset.not_nonempty_iff_eq_empty.mp h)]

end ThreeSumApsp.Spec

end
end

section


/-!
# Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30)

All three enumerations of Section 4 come from one: `nineStrs n lo hi`, the strings of n digits
0, …, 9 in which the digit 9 (the digit of P₀) occurs at least lo and at most hi times, in
lexicographic order.

* The boxes with e stars are the leaves with between e and m - t symbols P₀, with their e lowest
  symbols P₀ turned into stars (the proof of Lemma 29).
* The leaves of order below t contributing to an output string η (the paper's w) have, at the m
  levels of its inner set Q, a string with at least m - t + 1 nines (proof of Theorem 30).
* The boxes of η have, at the m levels of Q, a string with exactly m - t nines, the nines being the
  levels of V (Section 4.2).

The file proves what the list contains (`mem_nineStrs`), that it is increasing
(`pairwise_lt_nineStrs`), how long it is (`length_nineStrs`: ∑_f binom(n, f) 9^{n-f}), and how a
routine goes through it: it starts with `nineFirst` (`head?_nineStrs`), and `nineNext` goes from
each string to the next (`nineNext_getElem`); so the string reached after i steps,
`nineStr n lo hi i`, is the member number i (`getElem_nineStrs`).  Read from the right end of the
string, `nineNext` is one pass: skip the positions that cannot be raised, raise one digit
(`nineRaise`), and fill the rest with the least admissible string, zeros followed by nines.  The
proof follows the recursion of the list: the strings with the first digit d form a block,
`nineNext` goes through each block (`nextTo_map_cons`), and from the last string of a block to the
first string of the next block (`head_nineBlocks`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec































/-! ## The members of the list -/


































theorem length_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    l.length = n :=
  ((mem_nineStrs l).1 hl).1

/-- The digit of the star does not occur. -/
theorem ten_notMem_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    10 ∉ l :=
  fun h => absurd (((mem_nineStrs l).1 hl).2.1 10 h) (lt_irrefl 10)




































theorem nineStrs_nodup (n lo hi : ℕ) : (nineStrs n lo hi).Nodup :=
  (pairwise_lt_nineStrs n lo hi).imp fun h => ne_of_lt h

/-! ## The length of the list -/







































































/-! ## The first string -/









































/-! ## From each string to the next -/














































section

variable {n lo hi : ℕ}












































end
























section

variable {n lo hi i : ℕ}































end

end ThreeSumApsp.Spec

end
end

section


/-!
# What a query reads (proof of Theorem 30, "Query")

The output string, which the paper calls w, is η as a string of variables and w as the list of its
digits; the levels of its inner set Q are the positions of the digit 9.  w is also the list of
digits of the private leaf of η, and `scatter w s` replaces its m nines by a string s of m digits:
the paper's "forming its leaf or its box from the private leaf".  A query adds up the products at
the leaves of order below t contributing to η, and the stored values of the boxes of η (steps (2)
and (3) of the query in Section 4.3).

* `lowList`: the strings with at least m - t + 1 nines give the leaves of order below t ("Each of
  these leaves is obtained from the private leaf of w, which has P₀ at every level of Q, by picking
  fewer than t of those levels and replacing P₀ with one of the nine other terms at each of them");
* `boxesOf`: the strings with exactly m - t nines give the leaves of order exactly t, and `starRun`
  turns the leading nines into stars.  This is the second description of the boxes of w in
  Section 4.2: "For such a leaf, consider the lowest level of Q at which it chooses a term other
  than P₀, and replace its P₀ by a star at every lower level of Q (or at every level of Q, if
  t = 0).  The result is a box of w, and each box of w arises exactly once in this way".  On cubes
  the result is `starBelow`, and the members of the list are exactly the strings of the cubes
  `starBelow η τ` for these leaves τ (`mem_boxesOf_iff`; no other proof rests on this statement).
  In the first description the nines are the levels of V, and the leading nines those of F_V, which
  "is the longest initial segment of Q contained in V".  `starRunIf` is `starRun` as a pass over the
  string with one flag.

The results are `sum_lowList` and `sum_boxesOf` (a sum over one of the lists is the sum over the set
of the paper) and `sum_queryTerms_storedD` (the numbers that a query adds up have the sum of the
query of the paper). Each list is compared with its set by counting
(`List.sum_map_eq_sum_of_length_eq_card`):
1. The list has no repetitions: `scatter w` is injective on strings of m digits, and `starRun` can
   be undone (`lowList_nodup`, `boxesOf_nodup`).
2. Each member is the list of digits of a member of the set.  `scatter w s` is a leaf τ contributing
   to η with as many symbols P₀ as s has nines (`exists_leaf_scatter`).  With at least m - t + 1
   nines its order is below t (`exists_of_mem_lowList`).  With exactly m - t nines its order is t.
   The cube `starBelow η τ` has the digits of τ with stars at the levels of F_Z, where Z, the set
   of the levels of Q at which τ chooses P₀, is the nines of s.  `Unreached` is the formula for F_Z
   read on digits (`unreached_iff_mem_FV`); it holds exactly at the leading nines of s
   (`getD_scatter_starRun`), so the cube has the digits `scatter w (starRun s)`
   (`digitsC_starBelow`, `exists_leaf_of_mem_boxesOf`), and it is a box of η (`starBelow_mem`,
   `exists_of_mem_boxesOf`).
3. The lists have ∑_{d<t} α_d and α_t members (`length_lowList`, `length_boxesOf`), and so have the
   sets, by the last line of Lemma 28 (`lemma_28_counts`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec
































/-! ## Putting a string at the positions of the nines -/

private theorem scatter_nil_right (w : List ℕ) : scatter w [] = w := by
  cases w <;> rfl

/-- A digit other than 9 is kept. -/
theorem scatter_cons_of_ne {x : ℕ} (hx : x ≠ 9) (w s : List ℕ) :
    scatter (x :: w) s = x :: scatter w s := by
  cases s with
  | nil => rw [scatter_nil_right, scatter_nil_right]
  | cons d s => simp [scatter, hx]

/-- A digit 9 is replaced by the next digit of the string. -/
theorem scatter_nine_cons (w : List ℕ) (d : ℕ) (s : List ℕ) :
    scatter (9 :: w) (d :: s) = d :: scatter w s := by
  simp [scatter]

/-- The string has the length of w. -/
theorem length_scatter (w s : List ℕ) : (scatter w s).length = w.length := by
  fun_induction scatter w s <;> simp_all

/-- Every digit of `scatter w s` is a digit of w or of s. -/
private theorem mem_of_mem_scatter {w s : List ℕ} {d : ℕ} (h : d ∈ scatter w s) :
    d ∈ w ∨ d ∈ s := by
  fun_induction scatter w s <;> grind

/-- At a position where w has no 9, its digit is kept. -/
private theorem getD_scatter_of_ne (w s : List ℕ) (i : ℕ) (h : w.getD i 0 ≠ 9) :
    (scatter w s).getD i 0 = w.getD i 0 := by
  fun_induction scatter w s generalizing i <;> cases i <;> simp_all

/-- `scatter w s` has as many nines as s. -/
private theorem count_nine_scatter (w s : List ℕ) (hs : s.length = w.count 9) :
    (scatter w s).count 9 = s.count 9 := by
  fun_induction scatter w s <;> grind

/-- Strings of the right length are determined by what `scatter w` makes of them. -/
private theorem scatter_inj (w s s' : List ℕ) (hs : s.length = w.count 9)
    (hs' : s'.length = w.count 9) (h : scatter w s = scatter w s') : s = s' := by
  fun_induction scatter w s generalizing s' <;> cases s' <;> grind [scatter]

/-! ## The leading nines turned into stars -/

private theorem length_starRun (s : List ℕ) : (starRun s).length = s.length := by
  fun_induction starRun s <;> simp_all

/-- Turning the stars back into nines undoes `starRun`. -/
private theorem starsToNines_starRun {s : List ℕ} (h : 10 ∉ s) : starsToNines (starRun s) = s := by
  fun_induction starRun s with
  | case1 => rfl
  | case2 l ih => simp_all [starsToNines]
  | case3 d l hd => exact starsToNines_of_notMem h






















/-- The first position is not reached if it is a level of V. -/
private theorem unreached_cons_zero (x y : ℕ) (w u : List ℕ) :
    Unreached (x :: w) (y :: u) 0 ↔ x = 9 ∧ y = 9 := by
  rw [Unreached, ← Nat.and_forall_add_one]
  simp only [List.getD_cons_zero, lt_irrefl, Nat.zero_lt_succ, implies_true, and_true]
  tauto

/-- A later position is not reached if the first position is no level of Q ∖ V and the position is
not reached in the rest. -/
private theorem unreached_cons_succ (x y : ℕ) (w u : List ℕ) (i : ℕ) :
    Unreached (x :: w) (y :: u) (i + 1) ↔ (x = 9 → y = 9) ∧ Unreached w u i := by
  rw [Unreached, Unreached, ← Nat.and_forall_add_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.not_lt_zero, Nat.add_lt_add_iff_right]
  tauto

/-- Turning the leading nines of s into stars puts stars at the positions given by the formula for
F_V, and changes nothing else. -/
private theorem getD_scatter_starRun (w s : List ℕ) (hs : s.length = w.count 9) (i : ℕ) :
    (Unreached w (scatter w s) i → (scatter w (starRun s)).getD i 0 = 10) ∧
      (¬ Unreached w (scatter w s) i →
        (scatter w (starRun s)).getD i 0 = (scatter w s).getD i 0) := by
  induction w generalizing s i with
  | nil => simp [scatter, Unreached]
  | cons x w ih =>
    by_cases hx : x = 9
    · subst hx
      rw [List.count_cons_self] at hs
      obtain ⟨d, s, rfl⟩ := List.exists_cons_of_length_eq_add_one hs
      by_cases hd : d = 9
      · subst hd
        rw [starRun, if_pos rfl, scatter_nine_cons, scatter_nine_cons]
        cases i with
        | zero => simp [unreached_cons_zero]
        | succ i => simpa [unreached_cons_succ] using ih s (by simpa using hs) i
      · rw [starRun, if_neg hd, scatter_nine_cons]
        exact ⟨fun h => absurd (h.2 0 rfl hd) (Nat.not_lt_zero i), fun _ => rfl⟩
    · rw [List.count_cons_of_ne hx] at hs
      rw [scatter_cons_of_ne hx, scatter_cons_of_ne hx]
      cases i with
      | zero => simp [unreached_cons_zero, hx]
      | succ i => simpa [unreached_cons_succ, hx] using ih s hs i

/-! ## The leaves of order below t -/

section

variable {L m t : ℕ} {η : OutStr L}

/-- The output string has m nines. -/
private theorem count_nine_digitsO (hη : (innerSetO η).card = m) :
    (digitsO η).count 9 = m := by
  rw [← card_innerSetO, hη]

/-- A string of digits below 10, put at the levels of Q, gives a leaf contributing to η that
chooses P₀ as often as the string has a nine. -/
private theorem exists_leaf_scatter {s : List ℕ} (hlen : s.length = (digitsO η).count 9)
    (hdig : ∀ d ∈ s, d < 10) :
    ∃ τ : Leaf L, digitsT τ = scatter (digitsO η) s ∧ Leaf.Contributes τ η ∧
      (P0Levels τ).card = s.count 9 := by
  obtain ⟨τ, hτ⟩ := exists_digitsT (L := L) (scatter (digitsO η) s)
    (by rw [length_scatter, length_digitsO])
    fun d hd => (mem_of_mem_scatter hd).elim (digitsO_lt η d) (hdig d)
  refine ⟨τ, hτ, fun ℓ => ?_, ?_⟩
  · rw [contributes_iff, ← getD_digitsO, ← getD_digitsT, hτ]
    by_cases h9 : (digitsO η).getD ℓ 0 = 9
    · exact Or.inl h9
    · exact Or.inr (getD_scatter_of_ne _ _ _ h9)
  · rw [card_P0Levels, hτ, count_nine_scatter _ _ hlen]

/-- Every member of the list is the list of digits of a leaf of order below t contributing to η. -/
theorem exists_of_mem_lowList (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ lowList m t (digitsO η)) : ∃ τ ∈ lowLeaves m t η, digitsT τ = l := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hlen, hdig, hlo, -⟩ := (mem_nineStrs s).mp hs
  obtain ⟨τ, hτ, hcontr, hcard⟩ :=
    exists_leaf_scatter (hlen.trans (count_nine_digitsO hη).symm) hdig
  refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontr, ?_⟩, hτ⟩
  -- the order is m minus the number of nines, of which there are at least m - t + 1 (hlo)
  rw [order, hcard]
  omega

private theorem lowList_nodup (hη : (innerSetO η).card = m) : (lowList m t (digitsO η)).Nodup := by
  have hcount := count_nine_digitsO hη
  exact (nineStrs_nodup _ _ _).map_on fun s hs s' hs' h => scatter_inj _ s s'
    (by rw [length_of_mem_nineStrs hs, hcount]) (by rw [length_of_mem_nineStrs hs', hcount]) h

/-- There are ∑_{d < t} α_d such leaves. -/
theorem length_lowList (ht : t ≤ m) (w : List ℕ) :
    (lowList m t w).length = ∑ d ∈ Finset.range t, alpha m d := by
  rw [lowList, List.length_map, length_nineStrs]
  -- a string with f nines gives a leaf of order d = m - f: reflect the sum
  refine Finset.sum_nbij' (fun f => m - f) (fun d => m - d) ?_ ?_ ?_ ?_
    fun f hf => by rw [alpha, Nat.choose_symm (Finset.mem_Icc.mp hf).2]
  all_goals
    simp only [Finset.mem_Icc, Finset.mem_range]
    intro a ha
    omega

/-- **The first sum of a query**: a sum over the list is the sum over the leaves of order below t
contributing to η. -/
theorem sum_lowList (ht : t ≤ m) (hη : (innerSetO η).card = m) (F : List ℕ → ℤ) :
    ((lowList m t (digitsO η)).map F).sum = ∑ τ ∈ lowLeaves m t η, F (digitsT τ) :=
  List.sum_map_eq_sum_of_length_eq_card _ (lowList_nodup hη) _ digitsT (digitsT_injective L)
    (exists_of_mem_lowList hη)
    ((length_lowList ht _).trans (lemma_28_counts m t ht η hη).1.symm) F

/-! ## The boxes -/

/-- The formula for F_V on digits is the formula of the paper, for V = Z. -/
private theorem unreached_iff_mem_FV (τ : Leaf L) (ℓ : Fin L) :
    Unreached (digitsO η) (digitsT τ) ℓ ↔ ℓ ∈ FV (innerSetO η) (Zof (innerSetO η) τ) := by
  rw [Unreached, getD_digitsO_eq_nine, FV, Finset.mem_filter,
    forall_nine_digitsO η fun j => (digitsT τ).getD j 0 ≠ 9 → (ℓ : ℕ) < j]
  refine and_congr_right fun _ => ⟨fun h ℓ' hℓ' => ?_, fun h ℓ' hℓ' h9 => ?_⟩
  · obtain ⟨hQ, hZ⟩ := Finset.mem_sdiff.mp hℓ'
    refine h ℓ' hQ fun h9 => hZ (Finset.mem_filter.mpr ⟨hQ, ?_⟩)
    rwa [getD_digitsT, termIdx_eq_nine] at h9
  · refine h ℓ' (Finset.mem_sdiff.mpr ⟨hℓ', fun hZ => h9 ?_⟩)
    rw [getD_digitsT, termIdx_eq_nine]
    exact (Finset.mem_filter.mp hZ).2

/-- The cube of the second description of the boxes (Section 4.2): its digits are those of the leaf,
with the leading nines of the string at the levels of Q turned into stars. -/
private theorem digitsC_starBelow {τ : Leaf L} {s : List ℕ} (hs : s.length = (digitsO η).count 9)
    (hτ : digitsT τ = scatter (digitsO η) s) :
    digitsC (starBelow η τ) = scatter (digitsO η) (starRun s) := by
  refine digitsC_eq_of_getD _ (by rw [length_scatter, length_digitsO]) fun ℓ => ?_
  obtain ⟨hstar, hterm⟩ := getD_scatter_starRun (digitsO η) s hs ℓ
  rw [← hτ, unreached_iff_mem_FV] at hstar hterm
  rw [starBelow, Cube.starAt]
  split_ifs with h
  · exact hstar h
  · rw [hterm h, getD_digitsT, cubeIdx_term]

/-- Every member of the list arises, as in the second description of the boxes, from a leaf of order
exactly t contributing to η. -/
private theorem exists_leaf_of_mem_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ boxesOf m t (digitsO η)) :
    ∃ τ : Leaf L, (Leaf.Contributes τ η ∧ order m τ = t) ∧ digitsC (starBelow η τ) = l := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs s).mp hs
  have hlen' : s.length = (digitsO η).count 9 := hlen.trans (count_nine_digitsO hη).symm
  obtain ⟨τ, hτ, hcontr, hcard⟩ := exists_leaf_scatter hlen' hdig
  refine ⟨τ, ⟨hcontr, ?_⟩, digitsC_starBelow hlen' hτ⟩
  -- exactly m - t nines (hlo, hhi): the order is t
  rw [order, hcard]
  omega

/-- Every member of the list is the list of digits of a box of η: "The result is a box of w". -/
theorem exists_of_mem_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ boxesOf m t (digitsO η)) : ∃ π ∈ (Vsets m t η).biUnion (BV η), digitsC π = l := by
  obtain ⟨τ, ⟨hcontr, hord⟩, hl⟩ := exists_leaf_of_mem_boxesOf ht hη l h
  exact ⟨starBelow η τ, starBelow_mem hcontr hord, hl⟩

private theorem boxesOf_nodup (hη : (innerSetO η).card = m) : (boxesOf m t (digitsO η)).Nodup := by
  have hcount := count_nine_digitsO hη
  refine (nineStrs_nodup _ _ _).map_on fun s hs s' hs' h => ?_
  have hrun := scatter_inj _ (starRun s) (starRun s')
    (by rw [length_starRun, length_of_mem_nineStrs hs, hcount])
    (by rw [length_starRun, length_of_mem_nineStrs hs', hcount]) h
  rw [← starsToNines_starRun (ten_notMem_of_mem_nineStrs hs), hrun,
    starsToNines_starRun (ten_notMem_of_mem_nineStrs hs')]

/-- "This means that w has exactly α_t boxes." -/
theorem length_boxesOf (ht : t ≤ m) (w : List ℕ) : (boxesOf m t w).length = alpha m t := by
  rw [boxesOf, List.length_map, length_nineStrs, Finset.Icc_self, Finset.sum_singleton, alpha,
    Nat.choose_symm ht, Nat.sub_sub_self ht]

















/-- **The second sum of a query**: a sum over the list is the sum over the boxes of η. -/
theorem sum_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (F : List ℕ → ℤ) :
    ((boxesOf m t (digitsO η)).map F).sum = ∑ π ∈ (Vsets m t η).biUnion (BV η), F (digitsC π) :=
  List.sum_map_eq_sum_of_length_eq_card _ (boxesOf_nodup hη) _ digitsC (digitsC_injective L)
    (exists_of_mem_boxesOf ht hη)
    ((length_boxesOf ht _).trans (lemma_28_counts m t ht η hη).2.2.symm) F

end

/-! ## The query -/

/-- With the values of the dynamic program for the boxes, the numbers that a query adds up have the
sum of the query of the proof of Theorem 30. -/
theorem sum_queryTerms_storedD {L m t : ℕ} (ht : t ≤ m) (encA encB : Leaf L → ℤ) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    (queryTerms m t (arrT encA) (arrT encB) (storedD (arrT encA) (arrT encB)) (digitsO η)).sum
      = queryValue m t encA encB η := by
  rw [queryTerms, List.sum_append, queryValue, sum_lowList ht hη, sum_boxesOf ht hη,
    Finset.sum_biUnion (BV_pairwiseDisjoint η _)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun τ _ => leafProduct_digitsT encA encB τ)
    (Finset.sum_congr rfl fun V hV => Finset.sum_congr rfl fun π hπ => ?_)
  rw [storedD, dpValueD_digitsC, card_starLevels]

end ThreeSumApsp.Spec

end
end

section


/-!
# The boxes with e stars, as a list (proof of Lemma 29)

"A box in which f of the symbols are P₀ or stars is obtained from a leaf of order m - f (namely the
leaf we get by replacing its stars with P₀) by turning the e lowest symbols P₀ of that leaf into
stars, for some e ≤ f."  So the boxes with exactly e stars are the leaves with between e and m - t
symbols P₀, with the first e digits 9 turned into 10: this is `starBoxes`.

The list contains exactly the boxes with e stars (`mem_starBoxes`, `exists_of_mem_starBoxes`), each
of them once (`starBoxes_nodup`), so it has as many members as there are such boxes
(`length_starBoxes`), and all lists together have as many members as there are boxes
(`sum_length_starBoxes`).

The lists are the order of work of Lemma 29: "We compute the values of the boxes in increasing order
of their number of stars", "Generating the boxes with e stars and inserting them into the trie".
All of them go into the trie of the tile.  The number of stars can be read off a box
(`starCount_of_mem_starBoxes`), so boxes from different lists are different strings, and a string
is a box exactly if it is in the list for its number of stars (`isBoxDigits_digitsC`).  There are
boxes with e stars only for e ≤ m - t (`le_of_mem_starBoxes`).  Replacing the highest star of a box
with e + 1 stars by a term gives a box with e stars (`exists_lastStar_of_mem_starBoxes`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec













/-- A member of the list comes from a leaf with between e and m - t symbols P₀. -/
private theorem exists_leaf_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t e) :
    ∃ τ : Leaf L, e ≤ (P0Levels τ).card ∧ (P0Levels τ).card ≤ m - t ∧
      digitsC (starLowest e τ) = l := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs l').1 hl'
  obtain ⟨τ, rfl⟩ := exists_digitsT (L := L) l' hlen hdig
  exact ⟨τ, by rwa [card_P0Levels], by rwa [card_P0Levels], digitsC_starLowest e τ⟩

/-- The list contains exactly the boxes with e stars. -/
theorem mem_starBoxes {L : ℕ} (m t e : ℕ) (π : Cube L) :
    digitsC π ∈ starBoxes L m t e ↔ π ∈ boxesWithStars L m t e := by
  rw [mem_boxesWithStars]
  constructor
  · intro h
    obtain ⟨τ, hlo, hhi, hτ⟩ := exists_leaf_of_mem_starBoxes h
    obtain rfl : π = starLowest e τ := digitsC_injective L hτ.symm
    refine ⟨isBox_starLowest m t e τ hhi, ?_⟩
    rw [starLevels_starLowest, card_lowest]
    omega
  · rintro ⟨hbox, he⟩
    have hπ := eq_starLowest_starsToP0 π hbox.2
    have hcard := card_P0Levels_starsToP0 π
    rw [he] at hπ
    refine List.mem_map.2 ⟨digitsT (Cube.starsToP0 π),
      (mem_nineStrs _).2 ⟨length_digitsT _, digitsT_lt _, ?_, ?_⟩, ?_⟩
    · rw [← card_P0Levels]
      omega
    · rw [← card_P0Levels, hcard]
      exact hbox.1
    · rw [← digitsC_starLowest, ← hπ]

/-- Every member of the list is a cube. -/
theorem exists_of_mem_starBoxes {L m t e : ℕ} (l : List ℕ) (h : l ∈ starBoxes L m t e) :
    ∃ π : Cube L, digitsC π = l := by
  obtain ⟨τ, -, -, hτ⟩ := exists_leaf_of_mem_starBoxes h
  exact ⟨_, hτ⟩

/-- The number of stars can be read off a member of the list: the star is a symbol of its own, the
digit 10.  So boxes with different numbers of stars are different strings. -/
theorem starCount_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    starCount l = e := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  rw [← card_starLevels]
  exact (mem_boxesWithStars.1 ((mem_starBoxes m t e π).1 h)).2




theorem isBoxDigits_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    IsBoxDigits L m t l := by
  rwa [IsBoxDigits, starCount_of_mem_starBoxes h]

/-- A string of symbols is in the list of the boxes with its number of stars exactly if it is a
box. -/
theorem isBoxDigits_digitsC {L : ℕ} (m t : ℕ) (π : Cube L) :
    IsBoxDigits L m t (digitsC π) ↔ π ∈ boxes L m t := by
  rw [IsBoxDigits, ← card_starLevels, mem_starBoxes, mem_boxesWithStars, mem_boxes]
  exact and_iff_left rfl

/-- There are boxes with e stars only for e ≤ m - t. -/
theorem le_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) : e ≤ m - t := by
  obtain ⟨τ, hlo, hhi, -⟩ := exists_leaf_of_mem_starBoxes h
  exact hlo.trans hhi

/-- The members of the lists are strings of L digits below 11. -/
theorem starBoxes_digits {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    l.length = L ∧ ∀ d ∈ l, d < 11 := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  exact ⟨length_digitsC π, digitsC_lt π⟩

/-- Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars (proof
of Lemma 29). -/
theorem exists_lastStar_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t (e + 1)) :
    ∃ p, lastStar l = some p ∧ ∀ d < 10, l.set p d ∈ starBoxes L m t e := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  have hπ : π ∈ boxesWithStars L m t (e + 1) := (mem_starBoxes m t (e + 1) π).mp h
  have hcard : (Cube.starLevels π).card = e + 1 := (Finset.mem_filter.mp hπ).2
  have hne : (Cube.starLevels π).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨_, lastStar_digitsC π hne, fun d hd => ?_⟩
  have hsplit := lemma_29_split hπ hne (termEquiv.symm ⟨d, hd⟩)
  rw [← mem_starBoxes, digitsC_replace] at hsplit
  have hidx : ((termIdx (termEquiv.symm ⟨d, hd⟩) : Fin 10) : ℕ) = d :=
    congrArg Fin.val (termEquiv.apply_symm_apply ⟨d, hd⟩)
  rwa [hidx] at hsplit

/-- No box occurs twice in the list: turning the stars back into nines gives the leaf. -/
theorem starBoxes_nodup (L m t e : ℕ) : (starBoxes L m t e).Nodup := by
  refine (nineStrs_nodup _ _ _).map_on fun x hx y hy h => ?_
  rw [← starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hx), h,
    starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hy)]

/-- The list has as many members as there are boxes with e stars. -/
theorem length_starBoxes (L m t e : ℕ) :
    (starBoxes L m t e).length = (boxesWithStars L m t e).card := by
  classical
  have himage : (boxesWithStars L m t e).image digitsC = (starBoxes L m t e).toFinset := by
    ext l
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact (mem_starBoxes m t e π).2 hπ
    · intro hl
      obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l hl
      exact ⟨π, (mem_starBoxes m t e π).1 hl, rfl⟩
  rw [← List.toFinset_card_of_nodup (starBoxes_nodup L m t e), ← himage,
    Finset.card_image_of_injective _ (digitsC_injective L)]

/-- All lists together have as many members as there are boxes (Lemma 29). -/
theorem sum_length_starBoxes (L m t : ℕ) :
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length).sum
      = (boxes L m t).card := by
  have hfibres : (boxes L m t).card = ∑ e ∈ Finset.range (m - t + 1),
      ((boxes L m t).filter fun π => (Cube.starLevels π).card = e).card := by
    refine Finset.card_eq_sum_card_fiberwise fun π hπ => ?_
    have := (mem_boxes.1 (Finset.mem_coe.1 hπ)).1
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [List.sum_map_range, hfibres]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [length_starBoxes]
  refine congrArg Finset.card (Finset.ext fun π => ?_)
  rw [mem_boxesWithStars, Finset.mem_filter, mem_boxes]

end ThreeSumApsp.Spec

end
end

section


/-!
# Tries in one array (Section 4.3)

"for each tile we store its boxes, with their values, in a standard trie on their strings of L
symbols.  Thus […] looking up or inserting a box, takes O(L) operations."  Here a string is a list
of L digits below 11, for the ten terms and the star.

All tries live in one array of integers and are numbered; the number of a trie is the number of its
tile.  A vertex is a block of eleven consecutive cells, one for each symbol, holding the address of
the child, or 0 if there is none; a vertex at depth L holds the value of its box in its first cell.
A box is stored if the pointers for its L symbols lead from the root of the trie to such a vertex
(`trieWalk`).  A new vertex is appended at the end of the array (`trieNew`).  The two operations
are `trieInsert` and `trieLookup`.

The interface is `TrieRep`: "the array holds tries with these roots and these stored values".  It
holds for an array without tries (`TrieRep.empty`), it is kept by a new trie (`TrieRep.new`) and by
an insertion (`TrieRep.insert`), and it says what a lookup returns (`TrieRep.lookup`).  `WalkOK` and
`InsertOK` say in addition that every address met on the way lies inside the array
(`TrieRep.walkOK`, `TrieRep.insertOK`).

The proof.  The pair (i, w) names the vertex of trie number i to which the prefix w leads.  The
invariant `TrieInv` gives every vertex its address nd (i, w), 0 if there is none.  `TrieRep` says
that such an nd exists, with nd (i, []) = roots i and the value v in the cell nd x for every entry
f x = some v.
1. Three steps keep the invariant: a new root, a new child, a value written at depth L
   (`TrieInv.newRoot`, `TrieInv.newChild`, `TrieInv.setVal`).  The first gives `TrieRep.new`.
2. An insertion is a sequence of new children and then one write.  Each step extends the tries
   (`TrieExt`): no vertex moves, no root appears, no value of another string changes.  `Inserted`
   collects what holds at the end, and `trieInsert_spec` proves it by induction on the rest of the
   string.  This gives `TrieRep.insert` and `TrieRep.insertOK`.
3. A lookup goes from the vertex of a prefix to the vertex of the next prefix (`trieWalk_spec`).
   This gives `TrieRep.lookup` and `TrieRep.walkOK`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The operations -/


































/-- A vertex has eleven cells. -/
theorem length_trieNew (T : List ℤ) : (trieNew T).length = T.length + 11 := by
  simp [trieNew]

/-- An insertion adds at most one vertex for each symbol (proof of Lemma 29: "adds at most L
vertices per box"). -/
theorem length_trieInsert_le (T : List ℤ) (p : ℕ) (key : List ℕ) (v : ℤ) :
    (trieInsert T p key v).length ≤ T.length + 11 * key.length := by
  induction key generalizing T p with
  | nil => simp [trieInsert]
  | cons d l ih =>
    rw [trieInsert, List.length_cons]
    split_ifs
    · have := ih (trieNew (T.set (p + d) T.length)) T.length
      rw [length_trieNew, List.length_set] at this
      omega
    · have := ih T (T.getD (p + d) 0).toNat
      omega

end ThreeSumApsp.Spec

end

namespace ThreeSumApsp.Spec

/-! ## Arrays as functions -/













private theorem cells_trieNew (T : List ℤ) : cells (trieNew T) = cells T := by
  funext x
  simp only [cells, trieNew, List.getD_eq_getElem?_getD]
  by_cases hx : x < T.length
  · rw [List.getElem?_append_left hx]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : T.length ≤ x),
      List.getElem?_replicate]
    split_ifs <;> rfl

private theorem cells_of_le (T : List ℤ) (a : ℕ) (ha : T.length ≤ a) : cells T a = 0 := by
  simp [cells, List.getD_eq_getElem?_getD, List.getElem?_eq_none ha]

/-! ## The invariant -/




















namespace TrieInv

variable {L lo fr : ℕ} {μ : ℕ → ℤ} {nd : ℕ × List ℕ → ℕ}

/-- A vertex lies below the first free cell, and its address is not 0. -/
private theorem inside (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} (hx : nd x ≠ 0) :
    0 < nd x ∧ nd x + 11 ≤ fr :=
  ⟨Nat.pos_of_ne_zero hx, (h.range x hx).2.1⟩










/-- The prefixes of a prefix that has a vertex have vertices. -/
private theorem prefix_ne (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (l : List ℕ)
    (hw : nd (i, w ++ l) ≠ 0) : nd (i, w) ≠ 0 := by
  induction l using List.reverseRecOn with
  | nil => simpa using hw
  | append_singleton l a ih =>
    rw [← List.append_assoc] at hw
    exact ih (h.closed _ _ _ hw)

/-- A new vertex x at the address fr; its parent, if x is not a root, is a vertex already.  The
cells may change, as long as those from fr on stay free and the cells of the old vertices point to
the children, x among them. -/
private theorem addVertex (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} {μ' : ℕ → ℤ} (hx : nd x = 0)
    (hparent : ∀ i w a, (i, w ++ [a]) = x → nd (i, w) ≠ 0) (hfresh : ∀ c, fr ≤ c → μ' c = 0)
    (hchild : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 →
      μ' (nd (i, w) + a) = Function.update nd x fr (i, w ++ [a])) :
    TrieInv L lo μ' (Function.update nd x fr) (fr + 11) := by
  have hlo := h.lo_pos
  have hfr := h.fr_aligned
  refine { child := fun i w a hw ha hnd => ?_, range := fun y hnd => ?_,
           inj := fun y y' hnd heq => ?_, closed := fun i w a hnd => ?_,
           fresh := fun c hc => hfresh c (by omega), lo_pos := hlo,
           fr_aligned := ⟨by omega, by omega⟩ }
  · -- child
    by_cases hwx : (i, w) = x
    · -- the new vertex has no children
      have hne : (i, w ++ [a]) ≠ x := fun happ => by simp [← hwx] at happ
      have hnone : nd (i, w ++ [a]) = 0 := by
        by_contra hc
        exact h.closed _ _ _ hc (by rw [hwx, hx])
      rw [hwx, Function.update_self, Function.update_of_ne hne, hfresh _ (by omega), hnone]
      rfl
    · rw [Function.update_of_ne hwx] at hnd ⊢
      exact hchild i w a hw ha hnd
  · -- range
    rw [Function.update_apply] at hnd ⊢
    split_ifs at hnd ⊢
    · omega
    · have := h.range y hnd
      omega
  · -- inj: the new address is above all the old ones
    rw [Function.update_apply] at hnd
    rw [Function.update_apply, Function.update_apply] at heq
    split_ifs at hnd heq with hyx hyx'
    · rw [hyx, hyx']
    · have := h.range y' (by omega)
      omega
    · have := h.range y hnd
      omega
    · exact h.inj y y' hnd heq
  · -- closed
    by_cases hwx : (i, w) = x
    · rw [hwx, Function.update_self]
      omega
    · rw [Function.update_of_ne hwx]
      by_cases happ : (i, w ++ [a]) = x
      · exact hparent i w a happ
      · exact h.closed i w a (by rwa [Function.update_of_ne happ] at hnd)

/-- A new trie number i: its root is a new vertex at the address fr. -/
private theorem newRoot (h : TrieInv L lo μ nd fr) (i : ℕ) (hi : nd (i, []) = 0) :
    TrieInv L lo μ (Function.update nd (i, []) fr) (fr + 11) := by
  have hne : ∀ (j : ℕ) (w : List ℕ) (a : ℕ), (j, w ++ [a]) ≠ (i, []) := fun j w a happ => by
    simp at happ
  refine h.addVertex hi (fun j w a happ => absurd happ (hne j w a)) h.fresh
    fun j w a hw ha hnd => ?_
  rw [Function.update_of_ne (hne j w a), h.child j w a hw ha hnd]



































end TrieInv

/-! ## Insertion -/

































section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}








































































/-! ## Lookup -/

/-- **Lookup.**  Following the symbols of a string whose vertex exists leads to that vertex, through
addresses inside the array. -/
private theorem trieWalk_spec (hinv : TrieInv L lo (cells T) nd T.length) (key : List ℕ)
    (hlen : w.length + key.length ≤ L) (hkey : ∀ d ∈ key, d < 11) (hne : nd (i, w ++ key) ≠ 0) :
    WalkOK T (nd (i, w)) key ∧ trieWalk T (nd (i, w)) key = nd (i, w ++ key) := by
  induction key generalizing w with
  | nil =>
    rw [List.append_nil] at hne ⊢
    exact ⟨hinv.inside hne, rfl⟩
  | cons d l ih =>
    rw [List.length_cons] at hlen
    rw [List.append_cons] at hne ⊢
    have hwd : nd (i, w ++ [d]) ≠ 0 := hinv.prefix_ne l hne
    have hw : nd (i, w) ≠ 0 := hinv.prefix_ne [d] hwd
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) :=
      hinv.child i w d (by omega) (hkey d (by simp)) hw
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    obtain ⟨hok, hwalk⟩ := ih (w := w ++ [d])
      (by rw [List.length_append, List.length_singleton]; omega)
      (fun x hx => hkey x (by simp [hx])) hne
    rw [WalkOK, trieWalk, hchild, Int.toNat_natCast]
    exact ⟨⟨hpos, hin, by omega, hok⟩, hwalk⟩

end

/-! ## The interface -/

public section









namespace TrieRep

/-- An array without tries: any array of positive length.  The tries will be built behind it: lo is
its length. -/
theorem empty (L : ℕ) (T : List ℤ) (hT : 0 < T.length) :
    TrieRep L T.length T (fun _ => 0) fun _ => none :=
  -- no prefix has a vertex, so the fields on vertices hold vacuously
  ⟨fun _ => 0,
    { child := fun _ _ _ _ _ h => absurd rfl h, range := fun _ h => absurd rfl h,
      inj := fun _ _ h => absurd rfl h, closed := fun _ _ _ h => absurd rfl h,
      fresh := fun a ha => cells_of_le T a ha, lo_pos := hT,
      fr_aligned := ⟨Nat.le_refl _, by simp⟩ },
    fun _ => rfl, fun _ _ _ h => by simp at h⟩

variable {L lo : ℕ} {T : List ℤ} {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}

/-- The array is not empty: the address 0 means that there is no vertex. -/
theorem length_pos (h : TrieRep L lo T roots f) : 0 < T.length := by
  obtain ⟨nd, hinv, -, -⟩ := h
  exact Nat.lt_of_lt_of_le hinv.lo_pos hinv.fr_aligned.1

/-- Fewer stored values are a weaker claim. -/
theorem mono {g : ℕ × List ℕ → Option ℤ} (h : TrieRep L lo T roots f)
    (hg : ∀ x v, g x = some v → f x = some v) : TrieRep L lo T roots g := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  exact ⟨nd, hinv, hroots, fun i key v hx => hval i key v (hg _ v hx)⟩

/-- A new, empty trie number i. -/
theorem new (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i = 0) :
    TrieRep L lo (trieNew T) (Function.update roots i T.length) f := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  refine ⟨Function.update nd (i, []) T.length, ?_, fun j => ?_, fun j key v hf => ?_⟩
  · rw [cells_trieNew, length_trieNew]
    exact hinv.newRoot i (by rw [hroots, hi])
  · by_cases hsame : j = i
    · rw [hsame, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hsame, Function.update_of_ne (by simpa using hsame), hroots]
  · obtain ⟨hlen, hne, hv⟩ := hval j key v hf
    rw [Function.update_of_ne fun hkey => hne (by rw [hkey, hroots, hi]), cells_trieNew]
    exact ⟨hlen, hne, hv⟩






































/-- What `trieWalk_spec` says about the way from the root of trie number i down a stored string. -/
private theorem walk_spec (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ)
    (hd : ∀ d ∈ key, d < 11) (v : ℤ) (hf : f (i, key) = some v) :
    WalkOK T (roots i) key ∧ T.getD (trieWalk T (roots i) key) 0 = v := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  obtain ⟨hlen, hne, hv⟩ := hval i key v hf
  obtain ⟨hok, hwalk⟩ := trieWalk_spec (i := i) (w := []) hinv key (by simp [hlen]) hd hne
  rw [hroots] at hok hwalk
  exact ⟨hok, by rw [hwalk]; exact hv⟩

/-- Looking up a stored value. -/
theorem lookup (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ) (hd : ∀ d ∈ key, d < 11) (v : ℤ)
    (hf : f (i, key) = some v) : trieLookup T (roots i) key = v :=
  (h.walk_spec i key hd v hf).2

/-- On the way down a stored string, every cell read holds the address of a vertex inside the
array. -/
theorem walkOK (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ) (hd : ∀ d ∈ key, d < 11) (v : ℤ)
    (hf : f (i, key) = some v) : WalkOK T (roots i) key :=
  (h.walk_spec i key hd v hf).1

end TrieRep

end

end ThreeSumApsp.Spec

end

section


/-!
# The trie of a tile, and the tries of all tiles (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  `tileTrie` builds this trie.

"We compute the values of the boxes in increasing order of their number of stars": `fillUpTo` goes
through the boxes with 0, 1, … stars (`starBoxes`), and `fillTrie` inserts the boxes with e stars
with their values (`boxValue`): the value of a box without stars is "the product of its two numbers
in the encodings", the value of a box with stars is computed "with ten lookups in the trie" of the
tile.  `allTries` does this for all tiles, in one array; the number of a trie is the number of its
tile.  The array and the list of the roots form a record `TrieStore`.

What the array holds at a moment is a function from pairs (the number of a trie, a box) to values:
`storedUpTo` in the middle of a tile, `storedAll` between two tiles.
1. One more box is one more entry, the state after all boxes with k stars is the state before the
   first box with k + 1 stars, and a complete tile adds its boxes to `storedAll`
   (`storedUpTo_snoc`, `storedUpTo_succ`, `storedAll_snoc`).
2. Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars
   (`exists_lastStar_of_mem_starBoxes`); so, once the boxes with e stars are stored, the value
   computed for the box is that of the dynamic program (`boxValue_eq`).
3. So the array represents these functions, in the sense of `TrieRep`, after some boxes with e stars
   (`fillTrie_rep`), after all boxes with fewer than k stars (`fillUpTo_rep`) and after some tiles
   (`allTries_rep`).
4. Hence a lookup returns the value of the dynamic program of Lemma 29 (`lookup_allTries`), which is
   the value of the box: the array holds "for every tile, the values of all its boxes"
   (`lookup_allTries_eq_val`).  Every box that a query reads is there (`boxesOf_mem_starBoxes`).
5. Space: "O(L) […] space per box" (`length_tileTrie_le`, `length_allTries_le`).
6. The bottom line, for any list of tiles: the query that reads the values of its boxes from the
   trie of its tile (`trieQuery`) returns `queryValue` (`trieQuery_allTries`), and all its walks
   down the trie are safe (`walkOK_allTries`).  The tiles of the product are `tileList`, and
   `tilesBefore` is its part before a tile.

Two ladders lead from the arrays to the paper.
* A query: `trieQuery` adds up `queryTerms` with the values read from the trie; these are the values
  of the dynamic program (`queryTerms_allTries`), with which the sum is `queryValue` on cubes
  (`sum_queryTerms_storedD`), which is `querySum`, the sum of Lemma 28 (`lemma_29_values`, inside
  `Theorem30.correct`), which is the entry `(X * Y) I J` (`Theorem30.query`).
* The value of a box: `boxValue` reads from the trie; it is `dpValueD` on lists of digits
  (`boxValue_eq`), which is `dpValue` on cubes (`dpValueD_digitsC`), which is `Cube.val`
  (`lemma_29_values`).  `lookup_allTries_eq_val` is the whole ladder; no other proof rests on it.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Building the tries -/












namespace TrieStore














/-- The new trie has the next number, and its root is at the old end of the array. -/
theorem root_new (s : TrieStore) : s.new.root s.roots.length = s.cells.length := by
  simp [root, new]

/-- A new, empty trie changes no entry. -/
theorem Holds.new {L lo : ℕ} {s : TrieStore} {f : ℕ × List ℕ → Option ℤ} (h : s.Holds L lo f) :
    s.new.Holds L lo f := by
  have hroot : s.new.root = Function.update s.root s.roots.length s.cells.length :=
    List.getD_append_singleton _ _ _
  rw [Holds, hroot]
  exact TrieRep.new h _ (List.getD_eq_default _ _ le_rfl)

end TrieStore















































private theorem fillTrie_cons (encA encB : List ℤ) (root e : ℕ) (l : List ℕ)
    (boxes : List (List ℕ)) (T : List ℤ) :
    fillTrie encA encB root e (l :: boxes) T
      = fillTrie encA encB root e boxes (trieInsert T root l (boxValue encA encB T root e l)) := rfl

/-- The trie of one more tile is built on top of the tries of the tiles before it. -/
theorem allTries_snoc (L m t : ℕ) (tiles : List TileEnc) (ab : TileEnc) :
    allTries L m t (tiles ++ [ab]) = tileTrie ab.encA ab.encB L m t (allTries L m t tiles) := by
  simp [allTries, List.foldl_append]

/-- Every box that a query reads is a box of the tile. -/
private theorem boxesOf_mem_starBoxes {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) (l : List ℕ) (hl : l ∈ boxesOf m t (digitsO η)) :
    IsBoxDigits L m t l := by
  obtain ⟨π, hπ, rfl⟩ := exists_of_mem_boxesOf ht hη l hl
  obtain ⟨V, hV, hπ⟩ := Finset.mem_biUnion.mp hπ
  exact (isBoxDigits_digitsC m t π).mpr (Theorem30.lookup hV hπ)

/-! ## What the tries hold -/



















section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L m t : ℕ}

/-- The boxes with fewer than k stars are stored with the values of the dynamic program. -/
theorem storedUpTo_of_lt {k e : ℕ} (pre : List (List ℕ)) {l : List ℕ} (he : e < k)
    (hl : l ∈ starBoxes L m t e) :
    storedUpTo old i encA encB L m t k pre (i, l) = some (dpValueD encA encB e l) := by
  obtain rfl := starCount_of_mem_starBoxes hl
  simp [storedUpTo, storedD, he, hl]

/-- Before the first box, there are the old entries only. -/
private theorem storedUpTo_zero (x : ℕ × List ℕ) (v : ℤ)
    (h : storedUpTo old i encA encB L m t 0 [] x = some v) : old x = some v := by
  simpa [storedUpTo] using h

/-- One more box is one more entry. -/
private theorem storedUpTo_snoc {e : ℕ} (pre : List (List ℕ)) {l : List ℕ}
    (hl : l ∈ starBoxes L m t e) :
    storedUpTo old i encA encB L m t e (pre ++ [l]) =
      Function.update (storedUpTo old i encA encB L m t e pre) (i, l)
        (some (dpValueD encA encB e l)) := by
  funext ⟨n, l'⟩
  by_cases hx : (n, l') = (i, l)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    simp [storedUpTo, storedD, starCount_of_mem_starBoxes hl]
  · rw [Function.update_of_ne hx]
    have hne : ¬ (n = i ∧ l' = l) := fun ⟨hn, hl'⟩ => hx (by rw [hn, hl'])
    simp only [storedUpTo, List.mem_append, List.mem_singleton]
    -- the two conditions differ only at the key (i, l)
    exact if_congr (by tauto) rfl rfl

/-- The state after all boxes with k stars is the state before the first box with k + 1 stars. -/
private theorem storedUpTo_succ (k : ℕ) :
    storedUpTo old i encA encB L m t (k + 1) [] =
      storedUpTo old i encA encB L m t k (starBoxes L m t k) := by
  funext ⟨n, l⟩
  simp only [storedUpTo, List.not_mem_nil, or_false]
  refine if_congr (and_congr_right fun _ => ?_) rfl rfl
  rw [Nat.lt_succ_iff_lt_or_eq, or_and_right]
  exact or_congr_right
    ⟨fun h => h.1 ▸ h.2, fun h => ⟨starCount_of_mem_starBoxes h, isBoxDigits_of_mem_starBoxes h⟩⟩

end

/-- The boxes of tile number i are stored with the values of its dynamic program. -/
private theorem storedAll_of_mem {L m t : ℕ} {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
    {l : List ℕ} (hi : tiles[i]? = some ab) (hl : IsBoxDigits L m t l) :
    storedAll L m t tiles (i, l) = some (storedD ab.encA ab.encB l) := by
  simp [storedAll, hl, hi]

/-- One more tile: what is stored then was stored before or belongs to the new tile. -/
private theorem storedAll_snoc {L m t : ℕ} (tiles : List TileEnc) (ab : TileEnc)
    (x : ℕ × List ℕ) (v : ℤ) (h : storedAll L m t (tiles ++ [ab]) x = some v) :
    storedUpTo (storedAll L m t tiles) tiles.length ab.encA ab.encB L m t (m - t + 1) [] x
      = some v := by
  obtain ⟨n, l⟩ := x
  simp only [storedAll] at h
  split_ifs at h with hl
  simp only [storedUpTo]
  rcases Nat.lt_trichotomy n tiles.length with hn | hn | hn
  · -- an older tile
    rw [if_neg (by omega), ← h, List.getElem?_append_left hn]
    exact if_pos hl
  · -- the new tile
    rw [if_pos ⟨hn, Or.inl ⟨Nat.lt_succ_of_le (le_of_mem_starBoxes hl), hl⟩⟩, ← h, hn]
    simp
  · -- there is no such tile
    rw [List.getElem?_eq_none (by simp; omega)] at h
    simp at h

/-! ## The array represents what it should hold -/

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L lo m t e : ℕ}
  {roots : ℕ → ℕ}

/-- With the boxes with fewer stars stored, the value computed for a box is the value of the dynamic
program. -/
private theorem boxValue_eq {T : List ℤ} {pre : List (List ℕ)} {l : List ℕ}
    (h : TrieRep L lo T roots (storedUpTo old i encA encB L m t e pre))
    (hl : l ∈ starBoxes L m t e) : boxValue encA encB T (roots i) e l = dpValueD encA encB e l := by
  cases e with
  | zero => rfl
  | succ e =>
    obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hl
    exact sumAtLastStar_congr hp fun d hd => h.lookup i _ (starBoxes_digits (hset d hd)).2 _
      (storedUpTo_of_lt pre (Nat.lt_succ_self e) (hset d hd))

/-- Inserting boxes with e stars into the trie of the tile: if the array represents the state after
the boxes of pre, then after inserting the boxes of rest it represents the state after
pre ++ rest. -/
theorem fillTrie_rep (hi : roots i ≠ 0) (rest pre : List (List ℕ)) (T : List ℤ)
    (hmem : ∀ l ∈ rest, l ∈ starBoxes L m t e)
    (hrep : TrieRep L lo T roots (storedUpTo old i encA encB L m t e pre)) :
    TrieRep L lo (fillTrie encA encB (roots i) e rest T) roots
      (storedUpTo old i encA encB L m t e (pre ++ rest)) := by
  induction rest generalizing pre T with
  | nil => rwa [List.append_nil]
  | cons l rest ih =>
    have hl : l ∈ starBoxes L m t e := hmem l (by simp)
    have hins := hrep.insert i hi l (starBoxes_digits hl).1 (starBoxes_digits hl).2
      (boxValue encA encB T (roots i) e l)
    rw [boxValue_eq hrep hl, ← storedUpTo_snoc pre hl] at hins
    rw [fillTrie_cons, List.append_cons, boxValue_eq hrep hl]
    exact ih (pre ++ [l]) _ (fun x hx => hmem x (by simp [hx])) hins

end

/-- After k rounds the trie of the tile holds the values of the dynamic program for the boxes with
fewer than k stars, and the older entries are kept. -/
theorem fillUpTo_rep {old : ℕ × List ℕ → Option ℤ} (encA encB : List ℤ) {L lo : ℕ} (m t : ℕ)
    (s : TrieStore) (hs : s.Holds L lo old) (k : ℕ) :
    (tileTrieUpTo encA encB L m t s k).Holds L lo
      (storedUpTo old s.roots.length encA encB L m t k []) := by
  induction k with
  | zero => exact hs.new.mono storedUpTo_zero
  | succ k ih =>
    have hfill := fillTrie_rep (roots := s.new.root) (by rw [s.root_new]; exact hs.length_pos.ne')
      (starBoxes L m t k) [] _ (fun _ hl => hl) ih
    rw [storedUpTo_succ]
    rwa [s.root_new] at hfill

section

variable (L m t : ℕ)

/-- There is one root for each tile. -/
theorem length_roots_allTries (tiles : List TileEnc) :
    (allTries L m t tiles).roots.length = tiles.length := by
  induction tiles using List.reverseRecOn with
  | nil => rfl
  | append_singleton tiles ab ih =>
    rw [allTries_snoc, List.length_append, List.length_singleton, ← ih]
    exact List.length_append

/-- The tries of all tiles hold the values of the dynamic programs of the tiles. -/
theorem allTries_rep (tiles : List TileEnc) :
    (allTries L m t tiles).Holds L 1 (storedAll L m t tiles) := by
  induction tiles using List.reverseRecOn with
  | nil => exact (TrieRep.empty L [0] (by simp)).mono fun x v hx => by simp [storedAll] at hx
  | append_singleton tiles ab ih =>
    have h := fillUpTo_rep ab.encA ab.encB m t _ ih (m - t + 1)
    rw [length_roots_allTries] at h
    rw [allTries_snoc]
    exact h.mono (storedAll_snoc tiles ab)

variable {L m t} {tiles : List TileEnc} {i : ℕ}

/-- Looking up a box of tile number i. -/
theorem lookup_allTries {ab : TileEnc} (hi : tiles[i]? = some ab) {l : List ℕ}
    (hl : IsBoxDigits L m t l) : (allTries L m t tiles).lookup i l = storedD ab.encA ab.encB l :=
  (allTries_rep L m t tiles).lookup i l (starBoxes_digits hl).2 _ (storedAll_of_mem hi hl)










end

/-! ## Space -/

section

variable (encA encB : List ℤ)

/-- Inserting boxes "adds at most L vertices per box". -/
theorem length_fillTrie_le (root e L : ℕ) (boxes : List (List ℕ))
    (hb : ∀ l ∈ boxes, l.length = L) (T : List ℤ) :
    (fillTrie encA encB root e boxes T).length ≤ T.length + 11 * L * boxes.length := by
  induction boxes generalizing T with
  | nil => exact le_rfl
  | cons l boxes ih =>
    have hrest := ih (fun x hx => hb x (by simp [hx]))
      (trieInsert T root l (boxValue encA encB T root e l))
    have hins := length_trieInsert_le T root l (boxValue encA encB T root e l)
    rw [hb l (by simp)] at hins
    rw [fillTrie_cons, List.length_cons, Nat.mul_add_one]
    omega

variable (L m t : ℕ)

/-- The boxes with fewer than k stars take at most 11 L n cells, where n is their number. -/
theorem length_fillUpTo_le_sum (root k : ℕ) (T : List ℤ) :
    (fillUpTo encA encB L m t root k T).length
      ≤ T.length + 11 * L * ((List.range k).map fun e => (starBoxes L m t e).length).sum := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [fillUpTo, List.sum_range_succ, Nat.mul_add (11 * L)]
    have hfill := length_fillTrie_le encA encB root k L (starBoxes L m t k)
      (fun l hl => (starBoxes_digits hl).1) (fillUpTo encA encB L m t root k T)
    omega

/-- Lemma 29, space: "O(L) […] space per box"; eleven cells more for the root. -/
theorem length_tileTrie_le (s : TrieStore) :
    (tileTrie encA encB L m t s).cells.length
      ≤ s.cells.length + 11 * (1 + L * (boxes L m t).card) := by
  have h := length_fillUpTo_le_sum encA encB L m t s.cells.length (m - t + 1) (trieNew s.cells)
  rw [sum_length_starBoxes, Nat.mul_assoc, length_trieNew] at h
  exact h.trans (by omega)

/-- All tiles together: cell 0, and for each tile the space of Lemma 29. -/
theorem length_allTries_le (tiles : List TileEnc) :
    (allTries L m t tiles).cells.length
      ≤ 1 + tiles.length * (11 * (1 + L * (boxes L m t).card)) := by
  induction tiles using List.reverseRecOn with
  | nil => simp [allTries]
  | append_singleton tiles ab ih =>
    rw [allTries_snoc]
    refine (length_tileTrie_le _ _ L m t _).trans ?_
    rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

end

/-! ## The list of all tiles -/

section

variable {L : ℕ} (nB : ℕ) (encA encB : ℕ → Leaf L → ℤ)






/-- There are nB² tiles. -/
theorem length_tileList : (tileList nB encA encB).length = nB * nB :=
  List.length_flatMap_range nB _ fun _ _ => by simp

/-- Tile (β, β') has the number β nB + β'. -/
theorem getElem?_tileList {β β' : ℕ} (hβ : β < nB) (hβ' : β' < nB) :
    (tileList nB encA encB)[β * nB + β']? = some ⟨arrT (encA β), arrT (encB β')⟩ := by
  have hlt : β * nB + β' < (tileList nB encA encB).length :=
    (Nat.mul_add_lt_mul hβ hβ').trans_eq (length_tileList nB encA encB).symm
  rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem _ ⟨[], []⟩ hlt, tileList,
    List.getD_flatMap_range _ (fun _ _ => by simp) hβ hβ', List.getD_map_range _ hβ']






























end

/-! ## What the tries of all tiles give to a query

The query for tile number i gets the root of the trie of this tile. -/

section Query

variable {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
  (hi : tiles[i]? = some ab) {η : OutStr L} (hη : (innerSetO η).card = m)

include ht hi hη

/-- Every box of the query is stored: the walk down the trie is safe. -/
theorem walkOK_allTries {l : List ℕ} (hl : l ∈ boxesOf m t (digitsO η)) :
    WalkOK (allTries L m t tiles).cells ((allTries L m t tiles).root i) l := by
  have hbox := boxesOf_mem_starBoxes m t ht η hη l hl
  exact (allTries_rep L m t tiles).walkOK i l (starBoxes_digits hbox).2 _ (storedAll_of_mem hi hbox)

/-- The numbers that the query adds up, read from the trie, are those of the dynamic program. -/
theorem queryTerms_allTries :
    queryTerms m t ab.encA ab.encB ((allTries L m t tiles).lookup i) (digitsO η)
      = queryTerms m t ab.encA ab.encB (storedD ab.encA ab.encB) (digitsO η) :=
  congrArg _ (List.map_congr_left fun l hl =>
    lookup_allTries hi (boxesOf_mem_starBoxes m t ht η hη l hl))

end Query

/-- **The query on the tries of all tiles** returns the value of the query of the proof of
Theorem 30, which is the entry of the product (`Theorem30.correct`). -/
theorem trieQuery_allTries {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ}
    (encA encB : Leaf L → ℤ) (hi : tiles[i]? = some ⟨arrT encA, arrT encB⟩) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    trieQuery m t (arrT encA) (arrT encB) (allTries L m t tiles).cells
        ((allTries L m t tiles).root i) (digitsO η)
      = queryValue m t encA encB η :=
  (congrArg List.sum (queryTerms_allTries ht hi hη)).trans
    (sum_queryTerms_storedD ht encA encB hη)

end ThreeSumApsp.Spec

end
end

section


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/






















/-! ## Where the areas lie -/



















/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  have hWD : aWD p b0 = p.sharedEnd b0 := rfl
  have hCUR : aCUR p b0 = aWD p b0 + p.L := rfl
  have hBOX : aBOX p b0 = aCUR p b0 + p.L := rfl
  have hSS : aSS p b0 = aBOX p b0 + p.L := rfl
  have hFP : aFP p b0 = aSS p b0 + p.m := rfl
  have hROOTS : aROOTS p b0 = aFP p b0 + 1 := rfl
  have hTR : aTR p b0 = aROOTS p b0 + p.nB * p.nB := rfl
  have hTOP : top p t b0 = aTR p b0 + trieCap p t + 1 := rfl
  constructor <;> omega




























/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- The invariant depends only on the cells from b0 on, without the scratch strings WD, CUR, BOX,
SS. -/
theorem DSReady.congr (h : DSReady p t hmL aX aY b0 X Y μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩

/-- A memory that differs from one that holds the data structure only on the scratch strings WD,
CUR, BOX, SS holds it too. -/
theorem DSReady.of_same (h : DSReady p t hmL aX aY b0 X Y μ)
    (hs : SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)) : DSReady p t hmL aX aY b0 X Y μ' :=
  h.congr fun a _ ha => hs a ha






end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


/-!
# Strings, vertices and the coefficients of the encoding

Section 2.3.1. The recursion `Full` works on arrays indexed by strings of variables. This file has
the counts that the later cost estimates use: `7^L` left strings and `7^L` right strings of length
`L`, `10^k` vertices at depth `k` of the recursion tree, and coefficients `φ_λ(s)` and `ψ_λ(t)` in
`{0, ±1}`. The first three follow from the sizes of the alphabets; the last is a finite check. So is
the sentence that each form has at most three nonzero coefficients (`card_support_phi_le`,
`card_support_psi_le`), which no later proof uses. The example in the caption of Figure 3 is
`figure_3`.
-/

public section

open Finset

namespace ThreeSumApsp

/-- Section 2.3.1: an array on the left strings of length `L` "has 7^L entries in total". -/
theorem card_leftStr (L : ℕ) : Fintype.card (LeftStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_leftVar, Fintype.card_fin]

/-- Section 2.3.1: an array on the right strings of length `L` has `7^L` entries. -/
theorem card_rightStr (L : ℕ) : Fintype.card (RightStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_rightVar, Fintype.card_fin]





/-- Section 2.3.1: "φ_λ(s) ∈ {0, ±1}". -/
theorem abs_phi_le_one (lam : Term) (s : LeftVar) : |phi lam s| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: `ψ_λ(t) ∈ {0, ±1}`. -/
theorem abs_psi_le_one (lam : Term) (t : RightVar) : |psi lam t| ≤ 1 := by
  decide +revert



























end ThreeSumApsp

end
end

section


/-!
# Bounds on finite sums and products

General facts about sums and products over a finite set in an ordered ring or field.

* A sum of `s.card` numbers of absolute value at most `A` is at most `s.card * A` in absolute value
  (`Finset.abs_sum_le_card_mul`), also with coefficients of absolute value at most `1`
  (`Finset.abs_sum_mul_le`).
* A product of numbers of absolute value at most `1` has absolute value at most `1`
  (`Finset.abs_prod_le_one`). For integers, `Int.abs_le_one_iff` says that these are `0`, `1`, `-1`.
* A sum over the indices below `m * n` is a double sum (`Finset.sum_range_mul`).
* A part of a geometric series with ratio `0 < x < 1` is less than the whole series from its first
  term on (`geom_sum_Ico_lt_of_lt_one`).
-/

public section

namespace Finset

variable {ι R : Type*}

/-- If `|f i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, f i| ≤ s.card * A`. -/
theorem abs_sum_le_card_mul [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {f : ι → R}
    {A : R} (h : ∀ i ∈ s, |f i| ≤ A) : |∑ i ∈ s, f i| ≤ s.card * A :=
  (abs_sum_le_sum_abs f s).trans ((sum_le_card_nsmul s _ A h).trans_eq (nsmul_eq_mul _ _))

/-- If `|c i| ≤ 1` and `|a i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, c i * a i| ≤ s.card * A`. -/
theorem abs_sum_mul_le [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {c a : ι → R}
    {A : R} (hc : ∀ i ∈ s, |c i| ≤ 1) (ha : ∀ i ∈ s, |a i| ≤ A) :
    |∑ i ∈ s, c i * a i| ≤ s.card * A :=
  abs_sum_le_card_mul s fun i hi =>
    (abs_mul (c i) (a i)).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (hc i hi)).trans (ha i hi))

/-- If `|f i| ≤ 1` for all `i ∈ s`, then `|∏ i ∈ s, f i| ≤ 1`. -/
theorem abs_prod_le_one [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι)
    {f : ι → R} (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 :=
  (abs_prod s f).trans_le (prod_le_one (fun _ _ => abs_nonneg _) h)









end Finset













end
end

section


/-!
# Section 2.4.4: the remaining minutiae and the word size

* Minutiae.  The `K₀²` subsets, the tiles and the positions of `W` number `O(N² / D^{1/18})` in all
  (`minutiae_total_le`), because `K ≤ N` (`K_le_of_D_pow_le`), there are at most `4N²/N₀` tiles
  (`card_tiles_mul_N0_le`), `|W| ≤ 2^{-m} N²`, and `N, N₀ ≥ 2^{m/9}` (`two_rpow_le_of_D_pow_le`,
  `two_rpow_le_N0`).
* Word size.  An entry of an input array is an entry of `X` or `Y` or 0 (`abs_bandArrayL_le`,
  `abs_bandArrayR_le`); an encoded number is a `±1` combination of at most `7^L` of them
  (`abs_encodingL_le`, `abs_encodingR_le`); a value of `Pruned` is a sum of at most `10^L` products
  of two encoded numbers (`abs_Pruned_le`); and `10^L ≤ N²` by equation (6) (`ten_pow_le_sq`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The remaining minutiae -/






























































































/-! ### The word size -/

/-- The subsets in the table are distinct (Section 2.3.4), so a sum over the table that selects the
subset `Q` is one of its terms or 0. -/
private theorem sum_table_eq_zero_or {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (Q : Finset (Fin L)) :
    (∑ gh, if lay.table gh = Q then F gh else 0) = 0
      ∨ ∃ gh, (∑ gh', if lay.table gh' = Q then F gh' else 0) = F gh := by
  by_cases hQ : ∃ gh, lay.table gh = Q
  · obtain ⟨gh, rfl⟩ := hQ
    exact .inr ⟨gh, by simp [lay.table_injective.eq_iff]⟩
  · exact .inl (sum_eq_zero fun gh _ => if_neg (not_exists.mp hQ gh))

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a row band is an entry of `X` or 0.

NOTE.  `0 ≤ A` is needed only when `N = 0`. -/
theorem abs_bandArrayL_le {L m N : ℕ} (lay : Layout L m) {X : Matrix (Fin N) (Fin (D m)) ℤ} {A : ℤ}
    (hA : 0 ≤ A) (hX : ∀ I k, |X I k| ≤ A) (β : ℕ) (u : LeftStr L) :
    |bandArrayL lay X β u| ≤ A := by
  unfold bandArrayL arrayL bandFamilyL
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => rowBlock lay X (β * K0 L m + gh.1)) (innerSetL u)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hA
    · rw [hgh]
      unfold rowBlock padRows
      split_ifs
      · exact hX _ _
      · simpa using hA
  · simpa using hA

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a column band is an entry of `Y` or 0.

NOTE.  `0 ≤ B` is needed only when `N = 0`. -/
theorem abs_bandArrayR_le {L m N : ℕ} (lay : Layout L m) {Y : Matrix (Fin (D m)) (Fin N) ℤ} {B : ℤ}
    (hB : 0 ≤ B) (hY : ∀ k J, |Y k J| ≤ B) (β : ℕ) (v : RightStr L) :
    |bandArrayR lay Y β v| ≤ B := by
  unfold bandArrayR arrayR bandFamilyR
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => colBlock lay Y (β * K0 L m + gh.2)) (innerSetR v)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hB
    · rw [hgh]
      unfold colBlock padCols
      split_ifs
      · exact hY _ _
      · simpa using hB
  · simpa using hB

/-- A combination of the entries of an array, with a product of coefficients 0, 1 or -1 for each
entry, is at most the number of entries times the largest absolute value of an entry. -/
theorem abs_encodeWith_le {α : Type} [Fintype α] {c : Term → α → ℤ} (hc : ∀ lam s, |c lam s| ≤ 1)
    {L : ℕ} {a : (Fin L → α) → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodeWith c τ a| ≤ Fintype.card (Fin L → α) * A := by
  have h := abs_sum_mul_le univ (c := fun u => ∏ ℓ, c (τ ℓ) (u ℓ))
    (fun u _ => abs_prod_le_one _ fun ℓ _ => hc _ _) fun u _ => ha u
  simpa only [encodeWith, mul_comm, card_univ] using h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries", so its absolute value is at most `7^L` times the largest absolute value of an input
entry.  For the encoding of `a`. -/
theorem abs_encodingL_le {L : ℕ} {a : LeftStr L → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodingL a τ| ≤ 7 ^ L * A := by
  have h := abs_encodeWith_le abs_phi_le_one ha τ
  rw [card_leftStr] at h
  exact_mod_cast h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries".  For the encoding of `b`. -/
theorem abs_encodingR_le {L : ℕ} {b : RightStr L → ℤ} {B : ℤ} (hb : ∀ v, |b v| ≤ B) (τ : Leaf L) :
    |encodingR b τ| ≤ 7 ^ L * B := by
  have h := abs_encodeWith_le abs_psi_le_one hb τ
  rw [card_rightStr] at h
  exact_mod_cast h





































end ThreeSumApsp

end
end

section


/-!
# The block of Theorem 30: the directory, sizes and limits

Facts about the memory map and the invariant DSReady that the preprocessing and the query (proof of
Theorem 30) share.

* `dir_cell` gives a cell of the directory.
* The roots fill their area and the tries fit into theirs (`length_dsTries_roots`,
  `length_dsTries_le`).
* The limits: 10^L fits in a word (`Lim30.pow_le`), and the encoded numbers are at most 7^L U
  (`abs_enc_le`).
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {U : ℤ}
  {μ μ' : ℕ → ℤ}

/-! ## The directory -/

/-- A cell of the directory. -/
theorem dir_cell (h : Sec2.SharedReady p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ (b0 + j) = (((Sec2.dirList p aX aY b0).getD j 0 : ℕ) : ℤ) :=
  h.dir.read (by simpa [Sec2.dirList] using hj)

/-! ## Sizes and limits -/

/-- The number of roots: one for each tile. -/
theorem length_dsTries_roots (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    (dsTries p t hmL X Y).roots.length = p.nB * p.nB := by
  unfold dsTries
  rw [length_roots_allTries, length_tileList]

/-- The trie array fits into the trie area. -/
theorem length_dsTries_le (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    (dsTries p t hmL X Y).cells.length ≤ trieCap p t := by
  unfold dsTries trieCap
  have hle := length_allTries_le p.L p.m t (tileList p.nB (encRow p hmL X) (encCol p hmL Y))
  rwa [length_tileList] at hle

/-- The number 10^L of leaves fits in a word. -/
theorem Lim30.pow_le (h : Lim30 lim p t b0 U) : (10 : ℤ) ^ p.L ≤ lim.word := by
  refine le_trans ?_ h.pow
  push_cast
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Proof of Theorem 30, "Word size": the encoded numbers are at most 7^L U in absolute value. -/
theorem abs_enc_le (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) :
    (∀ τ, |encRow p hmL X β τ| ≤ 7 ^ p.L * U) ∧ ∀ τ, |encCol p hmL Y β' τ| ≤ 7 ^ p.L * U := by
  exact ⟨abs_encodingL_le (abs_bandArrayL_le (stdLayout hmL) hU hX β),
    abs_encodingR_le (abs_bandArrayR_le (stdLayout hmL) hU hY β')⟩

end Light.Sec4

end
end

section


/-!
# The cells of the directory, by name

The routines of Section 4 find the sizes and the addresses of the tables in the directory, the
first cells of the block.  `DirCells p b0 μ` says what the cells that they read hold, one equation
for each cell, under the name that the cell has in the program texts (`Dir.bands`, `Dir.encA`, …).
A proof that treats `x := mem[b0 + Dir.bands]` names the equation `bands`.  The shared stage
establishes all of them (`SharedReady.dirCells`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

















/-- After the shared stage the directory holds what `DirCells` says. -/
theorem _root_.Light.Sec2.SharedReady.dirCells {p : Sec2.Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ : ℕ → ℤ}
    (h : Sec2.SharedReady p hmL aX aY b0 X Y μ) : DirCells p b0 μ where
  levels := dir_cell h (j := Dir.levels) (by norm_num)
  inner := dir_cell h (j := Dir.inner) (by norm_num)
  outer := h.dir_read (j := Dir.outer) (by norm_num)
  blocks := h.dir_read (j := Dir.blocks) (by norm_num)
  bands := h.dir_read (j := Dir.bands) (by norm_num)
  leaves := h.dir_read (j := Dir.leaves) (by norm_num)
  mask := h.dir_read (j := Dir.mask) (by norm_num)
  band := h.dir_read (j := Dir.band) (by norm_num)
  block := h.dir_read (j := Dir.block) (by norm_num)
  digits := h.dir_read (j := Dir.digits) (by norm_num)
  encA := h.dir_read (j := Dir.encA) (by norm_num)
  encB := h.dir_read (j := Dir.encB) (by norm_num)
  sharedEnd := h.dir_read (j := Dir.sharedEnd) (by norm_num)

end Light.Sec4

end
end

section


/-!
# What outDigits writes is the output string of the position

Nothing here is about programs.  The digits of the output string of a position are those that
outDigits writes (`digitsO_outStrOfPos`): both lists are the `L` digits of the code of the string
(`digitList_ofDigitList`, `digitList_outCodeOfPos`).
-/

public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The digits of the output string of a position -/

/-- The digits of the output string of the position (I, J), for the computable layout. -/
theorem digitsO_outStrOfPos {L m : ℕ} (hmL : m ≤ L) (I J : ℕ) :
    digitsO (outStrOfPos (stdLayout hmL) I J) = outDigitsOfPos L m I J := by
  have hdigits := digitList_ofDigitList _ (digitsO_lt (outStrOfPos (stdLayout hmL) I J))
  rw [length_digitsO, ofDigitList_digitsO, codeO_outStrOfPos, digitList_outCodeOfPos] at hdigits
  exact hdigits.symm

end Light.Sec4

end
end

section


/-!
# Bounds on the partial sums (proof of Theorem 30, "Word size")

"every value we compute is a sum of at most 10^m products of two such numbers".  A routine that adds
up numbers one after the other holds, at every moment, the sum of an initial part of a list.  This
file bounds all these sums, for two encodings whose entries are at most A and B in absolute value.

* What the dynamic program of Lemma 29 computes for a cube with e stars is at most 10^e A B
  (`abs_dpValue_le`), and so is every sum of an initial part of the ten values that it adds up
  for the cube (`abs_dp_partial_sum_le`).
* The numbers that a query adds up stand for disjoint sets of leaves contributing to its output
  string η (the paper's w), of which there are 10^m (`Lemma28.card_leaves`); so every sum of an
  initial part of them is at most 10^m A B (`abs_query_partial_sum_le`).
-/

public section

namespace ThreeSumApsp.Spec

variable {L : ℕ} {encA encB : Leaf L → ℤ} {A B : ℤ} (hA : ∀ τ, |encA τ| ≤ A)
  (hB : ∀ τ, |encB τ| ≤ B)

include hA hB

/-! ## The dynamic program of Lemma 29 -/






/-- The product at a leaf is at most A B in absolute value. -/
private theorem abs_mul_le (τ : Leaf L) : |encA τ * encB τ| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul (hA τ) (hB τ) (abs_nonneg _) ((abs_nonneg _).trans (hA τ))






















/-- What the dynamic program on digits computes for a cube at depth e is at most 10^e A B in
absolute value. -/
private theorem abs_dpValueD_le (e : ℕ) (π : Cube L) :
    |dpValueD (arrT encA) (arrT encB) e (digitsC π)| ≤ 10 ^ e * (A * B) := by
  rw [dpValueD_digitsC]
  exact abs_dpValue_le hA hB e π





















/-! ## A query -/

/-- Every sum of an initial part of the numbers that a query adds up is at most 10^m A B in absolute
value: the numbers stand for disjoint sets of leaves contributing to η, of which there are 10^m. -/
theorem abs_query_partial_sum_le {m t : ℕ} (ht : t ≤ m) {η : OutStr L}
    (hη : (innerSetO η).card = m) (k : ℕ) :
    |((queryTerms m t (arrT encA) (arrT encB) (storedD (arrT encA) (arrT encB))
        (digitsO η)).take k).sum| ≤ 10 ^ m * (A * B) := by
  have hcount : ((lowLeaves m t η).card : ℤ)
      + ∑ π ∈ (Vsets m t η).biUnion (BV η), ((Cube.leaves π).card : ℤ) = 10 ^ m := by
    exact_mod_cast Lemma28.card_leaves m t ht η hη
  refine (List.abs_sum_take_le_sum_abs _ k).trans ?_
  rw [queryTerms, List.map_append, List.sum_append, List.map_map, List.map_map,
    sum_lowList ht hη, sum_boxesOf ht hη]
  calc _ ≤ ∑ _τ ∈ lowLeaves m t η, A * B
        + ∑ π ∈ (Vsets m t η).biUnion (BV η), ((Cube.leaves π).card : ℤ) * (A * B) := by
        refine add_le_add (Finset.sum_le_sum fun τ _ => ?_) (Finset.sum_le_sum fun π _ => ?_)
        · -- a leaf stands for itself
          simp only [Function.comp]
          rw [leafProduct_digitsT]
          exact abs_mul_le hA hB τ
        · -- a box with e stars stands for its 10^e leaves
          simp only [Function.comp, storedD]
          rw [Cube.card_leaves, card_starLevels]
          push_cast
          exact abs_dpValueD_le hA hB _ π
    _ = 10 ^ m * (A * B) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← add_mul, hcount]

end ThreeSumApsp.Spec

end
end

section


/-!
# A query, from the block that holds the data structure (proof of Theorem 30, "Query")

"Given (I, J), we find its tile from the bands of row I and column J, the subset Q of its block
product, and its output string w […], all in O(L) operations". Below, the output string is called η.
queryAt(I, J, b0) has four parts. It reads the sizes, the addresses of the tables and the bands of I
and J from the block at b0 (queryAtReads), computes the addresses of the areas of Section 4
(queryAtAreas), lets outDigits write the digits of η (queryAtOut), reads the root of the trie of the
tile from the table of roots, and lets queryCore compute the sum of Lemma 28 from the two encodings
and this trie (queryAtCore). There is one lemma for each part; for each of the two calls a record
holds the arguments (outArgs, coreArgs) and a lemma says that the block holds what the routine
assumes (outArgs_pre, coreArgs_pre). queryAt_spec puts the four parts together.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace QueryAt



























end QueryAt























































section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first two parts -/

/-- The first part reads the sizes, the addresses of the tables, and the two bands. -/
theorem queryAtReads_spec (hlim : Lim30 lim p t b0 U) (hds : DSReady p t hmL aX aY b0 X Y μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) :
    Ends lim P d queryAtReads ⟨frame [(I : ℤ), (J : ℤ), (b0 : ℤ)], μ⟩ 90
      (· = ⟨frame (queryAtRead p t b0 I J), μ⟩) := by
  have hw := hlim.std.space_le
  have hdir : b0 + 31 < lim.space ∧ p.aBAND b0 + p.N ≤ lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have dir := hds.shared.dirCells
  have cellT : μ ((b0 : ℤ) + 31).toNat = (t : ℕ) :=
    (congrArg μ (toNat_natCast_add_natCast b0 31)).trans hds.cellT
  have bandI := hds.shared.band I hI
  have bandJ := hds.shared.band J hJ
  -- levels := dir[0]; inner := dir[1]; switch := dir[31]; outer := dir[4]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.L : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.levels]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.levels] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.levels] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.m : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.inner]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.inner] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.inner] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (t : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cellT]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [cellT] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, cellT] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.Lo : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.outer]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.outer] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.outer] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- blocks := dir[7]; bands := dir[9]; leaves := dir[10]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.K0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.blocks]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.blocks] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.blocks] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.nB : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.bands]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.bands] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.bands] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.T : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.leaves]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.leaves] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.leaves] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- bandTab := dir[22]; blockTab := dir[23]; digitTab := dir[24]; digits := dir[30]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aBAND b0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.band]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.band] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.band] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aBLOCK b0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.block]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.block] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.block] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aDIG3 b0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.digits]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.digits] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.digits] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aWD p b0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.sharedEnd]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.sharedEnd] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.sharedEnd] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- bandI := bandTab[I]; bandJ := bandTab[J]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (I / (p.K0 * p.N0) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bandI]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [bandI] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, bandI] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (J / (p.K0 * p.N0) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bandJ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [bandJ] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, bandJ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  rfl

/-- The second part computes the addresses of the areas of Section 4. -/
theorem queryAtAreas_spec (hlim : Lim30 lim p t b0 U) (I J : ℕ) :
    Ends lim P d queryAtAreas ⟨frame (queryAtRead p t b0 I J), μ⟩ 50
      (· = ⟨frame (queryAtLocals p t b0 I J), μ⟩) := by
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hlim.std))
  obtain ⟨⟩ := areas p t b0
  unfold queryAtLocals queryAtRead
  -- the product nB², in the integers
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have hsq0 : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at htr
  -- box := digits + L + L; str := box + L; roots := str + m + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aBOX p b0 : ℕ) ?_ ?_ ?_);
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
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aSS p b0 : ℕ) ?_ ?_ ?_);
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
          (aROOTS p b0 : ℕ)
            -- tries := roots + nB nB
            
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
  -- tries := roots + nB nB
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aTR p b0 : ℕ) ?_ ?_ ?_);
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
  rfl

/-! ## The call of outDigits -/

/-- Bits as natural numbers. -/
theorem segN_of_segB {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : Sec2.SegB μ a l) :
    SegN μ a (l.map fun b => if b then 1 else 0) := by
  unfold Sec2.SegB at h
  unfold SegN
  rw [List.map_map]
  convert h using 2
  funext b
  cases b <;> simp






/-- The block holds what outDigits assumes. -/
theorem outArgs_pre (hlim : Lim30 lim p t b0 U) (hds : DSReady p t hmL aX aY b0 X Y μ) {I J : ℕ}
    (hI : I < p.N) (hJ : J < p.N) : OutDigitsPre lim μ (outArgs p b0 I J) := by
  have hgI : I / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hgJ : J / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hidx : I / p.N0 % p.K0 * p.K0 + J / p.N0 % p.K0 < p.KK := Nat.mul_add_lt_mul hgI hgJ
  -- the three tables lie below WD, and WD inside the memory
  have hsp := hlim.space
  have hmaskI := Nat.mul_add_le_mul hidx (le_refl p.L)
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hLo : p.L - p.m = p.Lo := rfl
  obtain ⟨⟩ := areas p t b0
  refine'
    { std := hlim.std
      m_le := hmL
      gI_lt := hgI
      gJ_lt := hgJ
      index_lt := tableIndex_lt p.L p.m (⟨_, hgI⟩, ⟨_, hgJ⟩)
      segMask := segN_of_segB (hds.shared.mask _ hidx)
      segI := hds.shared.dig3 I hI
      segJ := hds.shared.dig3 J hJ
      lenI := length_digitList ..
      lenJ := length_digitList ..
      ltI := fun _ => lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => lt_of_mem_digitList (by norm_num)
      spaceMasks := by change p.aMASK b0 + p.KK * p.L < lim.space; omega
      .. }
  -- the six fields that are left: the tables lie apart from WD, and all within the memory
  all_goals
    simp only [outArgs, OutDigitsArgs.base]
    omega

/-- The third part writes the digits of the output string of (I, J) at WD. -/
theorem queryAtOut_spec (hOut : OutDigitsSpec lim P) (hlim : Lim30 lim p t b0 U)
    (hds : DSReady p t hmL aX aY b0 X Y μ) {I J : ℕ} (hI : I < p.N) (hJ : J < p.N)
    (hd : d + 1 ≤ lim.depth) :
    Ends lim P d queryAtOut ⟨frame (queryAtLocals p t b0 I J), μ⟩ (tOutDigits p.L + 40) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ'⟩ ∧
        SegN μ' (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J)) ∧
        SameOutside μ μ' (aWD p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := outArgs_pre hlim hds hI hJ
  have blockI := hds.shared.block I hI
  have blockJ := hds.shared.block J hJ
  have hsp := hlim.space
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hbound : b0 + 31 < lim.space ∧ p.aBLOCK b0 + p.N ≤ lim.space ∧
      p.aDIG3 b0 + p.N * p.Lo ≤ lim.space := by
    obtain ⟨⟩ := areas p t b0
    omega
  have hprodI : ((p.aDIG3 b0 + I * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + I * p.Lo ≤ lim.space)
  have hprodJ : ((p.aDIG3 b0 + J * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + J * p.Lo ≤ lim.space)
  have hI0 : (0 : ℤ) ≤ (I : ℤ) * p.Lo := by positivity
  have hJ0 : (0 : ℤ) ≤ (J : ℤ) * p.Lo := by positivity
  push_cast at hprodI hprodJ
  -- outDigits(blockTab[I], blockTab[J], digitTab + I (L - m), digitTab + J (L - m), dir[21], …)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen ((hOut _ μ hpre) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (hOut _ μ hpre) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
                hds.shared.dirCells.mask]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
                hds.shared.dirCells.mask] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, queryAtLocals, queryAtRead,
                outArgs, blockI, blockJ, hds.shared.dirCells.mask] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ' h); (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨r, μ', rfl, ?_, h.2⟩
  rw [digitsO_outStrOfPos]
  exact h.1

/-! ## The call of queryCore -/























/-- Every product of two encoded numbers fits in a word. -/
theorem abs_enc_mul_le (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) (τ : Leaf p.L) :
    |encRow p hmL X β τ * encCol p hmL Y β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY β β'
  rw [abs_mul]
  calc |encRow p hmL X β τ| * |encCol p hmL Y β' τ| ≤ (7 ^ p.L * U) * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ lim.word := hlim.value

section Tile

variable (I J : Fin p.N)

/-- The tile of the position (I, J) is one of the nB² tiles. -/
theorem tileOf_lt (hmL : p.m ≤ p.L) : tileOf p I J < p.nB * p.nB :=
  Nat.mul_add_lt_mul (bandOf_lt_numBands hmL p.N I I.isLt) (bandOf_lt_numBands hmL p.N J J.isLt)

/-- It is given by the encodings of the band of I and of the band of J. -/
theorem getElem?_tileOf :
    (tileList p.nB (encRow p hmL X) (encCol p hmL Y))[tileOf p I J]?
      = some ⟨arrT (coreArgs p t hmL b0 X Y I J).encA, arrT (coreArgs p t hmL b0 X Y I J).encB⟩ :=
  getElem?_tileList p.nB _ _ (bandOf_lt_numBands hmL p.N I I.isLt)
    (bandOf_lt_numBands hmL p.N J J.isLt)

variable (ht : t ≤ p.m)

include ht

/-- Every box of the query is found in the trie of the tile. -/
theorem coreArgs_walk (l : List ℕ)
    (hl : l ∈ boxesOf p.m t (digitsO (coreArgs p t hmL b0 X Y I J).η)) :
    WalkOK (coreArgs p t hmL b0 X Y I J).T (coreArgs p t hmL b0 X Y I J).root l :=
  walkOK_allTries ht (getElem?_tileOf (t := t) (b0 := b0) I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J) hl

/-- Every partial sum of the query fits in a word. -/
theorem coreArgs_sums (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (j : ℕ) :
    |((coreArgs p t hmL b0 X Y I J).terms.take j).sum| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY ((I : ℕ) / (p.K0 * p.N0))
    ((J : ℕ) / (p.K0 * p.N0))
  have hcard := card_innerSetO_outStrOfPos (stdLayout hmL) I J
  have hterms := queryTerms_allTries ht
    (getElem?_tileOf (t := t) (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J) hcard
  rw [QueryCoreArgs.terms]
  exact (congrArg (fun l => |(l.take j).sum|) hterms).trans_le
    ((abs_query_partial_sum_le hrow hcol ht hcard j).trans hlim.value)

/-- What queryCore returns for the tile of (I, J) is (XY)[I, J], by Theorem 30. -/
theorem coreArgs_value :
    trieQuery p.m t (arrT (coreArgs p t hmL b0 X Y I J).encA)
      (arrT (coreArgs p t hmL b0 X Y I J).encB) (coreArgs p t hmL b0 X Y I J).T
      (coreArgs p t hmL b0 X Y I J).root (digitsO (coreArgs p t hmL b0 X Y I J).η) = (X * Y) I J :=
  (trieQuery_allTries ht _ _ (getElem?_tileOf I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J)).trans
    (Theorem30.correct t ht (stdLayout hmL) X Y I J)

end Tile

/-- The block, with the digits of the output string at WD, holds what queryCore assumes. -/
theorem coreArgs_pre (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReady p t hmL aX aY b0 X Y μ) (I J : Fin p.N)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    QueryCorePre lim μ (coreArgs p t hmL b0 X Y I J) := by
  have hU : 0 ≤ U := (abs_nonneg _).trans (hX I ⟨0, Nat.pow_pos (by norm_num)⟩)
  have hβ : (I : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N I I.isLt
  have hβ' : (J : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N J J.isLt
  -- the encodings lie below WD, the tries behind the scratch strings
  have hsp := hlim.space
  have hlen := length_dsTries_le p t hmL X Y
  have hrowA := Nat.mul_add_le_mul hβ (le_refl p.T)
  have hrowB := Nat.mul_add_le_mul hβ' (le_refl p.T)
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  refine'
    { std := hlim.std
      t_le := ht
      card := card_innerSetO_outStrOfPos (stdLayout hmL) I J
      segA := hds.shared.encA _ hβ
      segB := hds.shared.encB _ hβ'
      segT := hds.trie
      segDigits := hwd
      walk := coreArgs_walk I J ht
      sums := coreArgs_sums I J ht hlim hU hX hY
      prod := abs_enc_mul_le hlim hU hX hY _ _
      pow := hlim.pow_le
      .. }
  -- the fifteen fields that are left: the areas lie apart from each other and within the memory
  all_goals
    simp only [coreArgs]
    omega

/-- The fourth part returns (XY)[I, J] and changes the scratch strings BOX and SS only. -/
theorem queryAtCore_spec (hCore : QueryCoreSpec lim P) (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReady p t hmL aX aY b0 X Y μ)
    (I J : Fin p.N) (hd : d + 2 ≤ lim.depth) (r : ℤ)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    Ends lim P d queryAtCore ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ⟩
      (tQueryCore p.L p.m t + 60) fun σ' =>
        σ'.loc 0 = (X * Y) I J ∧ SameOutside2 μ σ'.mem (aSS p b0) p.m (aBOX p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := coreArgs_pre ht hlim hX hY hds I J hwd
  have hvalue := coreArgs_value (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J ht
  have dir := hds.shared.dirCells
  have htile := tileOf_lt I J hmL
  have cellRoot : μ (aROOTS p b0 + tileOf p I J)
      = ((dsTries p t hmL X Y).root (tileOf p I J) : ℕ) :=
    hds.roots.read (by rw [length_dsTries_roots]; exact htile)
  have hdir : b0 + 31 < lim.space ∧ aROOTS p b0 + p.nB * p.nB < lim.space := by
    have hsp := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have hmeets := (hCore _ μ hpre _ (by omega))
  have hencA := hpre.aA_lt
  have hencB := hpre.aB_lt
  simp only [coreArgs, tileOf] at hmeets hvalue hencA hencB htile cellRoot
  unfold queryAtLocals queryAtRead
  -- the bands, the root and 10^L become variables; the products in the arguments, in the integers
  generalize 10 ^ p.L = leaves at hencA hencB
  generalize (I : ℕ) / (p.K0 * p.N0) = β at *
  generalize (J : ℕ) / (p.K0 * p.N0) = β' at *
  generalize (dsTries p t hmL X Y).root (β * p.nB + β') = root at *
  have hencA' : ((p.aENCA b0 + β * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hencB' : ((p.aENCB b0 + β' * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have hroot' : ((aROOTS p b0 + (β * p.nB + β') : ℕ) : ℤ) < lim.space := by
    exact_mod_cast (by omega)
  have hrow0 : (0 : ℤ) ≤ (β : ℤ) * p.T := by positivity
  have hcol0 : (0 : ℤ) ≤ (β' : ℤ) * p.T := by positivity
  have hband0 : (0 : ℤ) ≤ (β : ℤ) * p.nB := by positivity
  have haddr : ((aROOTS p b0 : ℤ) + ((β : ℤ) * p.nB + β')).toNat
      = aROOTS p b0 + (β * p.nB + β') := by exact_mod_cast Int.toNat_natCast _
  push_cast at hencA' hencB' hroot'
  -- queryCore(dir[26] + bandI 10^L, dir[27] + bandJ 10^L, tries, roots[bandI nB + bandJ], …)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen (hmeets _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hmeets ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.encA, dir.encB, haddr, cellRoot]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.encA, dir.encB, haddr, cellRoot] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.encA, dir.encB, haddr,
                cellRoot] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r' μ' h); (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨?_, h.2⟩
  simp only [setLocal, List.cons_append, frame, List.getD_cons_zero]
  rw [h.1, hvalue]

/-! ## The routine -/

/-- **queryAt** meets its specification. -/
theorem queryAt_spec_sourceProof (hP : P[Proc.queryAt]? = some queryAtBody) (hOut : OutDigitsSpec lim P)
    (hCore : QueryCoreSpec lim P) : QueryAtSpec lim P := by
  intro p t hmL aX aY b0 X Y U μ I J ht hlim hX hY hds
  refine fun d hd => ⟨queryAtBody, hP, ?_⟩
  unfold tQueryAt
  -- the sizes, the tables, the bands
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (queryAtReads_spec hlim hds I.isLt J.isLt) ?_ ?_
      |
        refine
          Light.Ends.pieceLast (queryAtReads_spec hlim hds I.isLt J.isLt) ?_ ?_);
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
    (on_goal -1 => rintro _ rfl)
  -- the areas
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (queryAtAreas_spec hlim I J) ?_ ?_
      | refine Light.Ends.pieceLast (queryAtAreas_spec hlim I J) ?_ ?_);
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
    (on_goal -1 => rintro _ rfl)
  -- the digits of the output string, which change WD only
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen
            (queryAtOut_spec hOut hlim hds I.isLt J.isLt (by omega)) ?_ ?_
      |
        refine
          Light.Ends.pieceLast
            (queryAtOut_spec hOut hlim hds I.isLt J.isLt (by omega)) ?_ ?_);
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
    (on_goal -1 => rintro _ ⟨r, μ₁, rfl, hwd, same₁⟩)
  have same₁' : SameOutside μ μ₁ (aWD p b0) (3 * p.L + p.m) := same₁.mono le_rfl (by omega)
  -- the sum of Lemma 28, which changes BOX and SS only
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen
            (queryAtCore_spec hCore ht hlim hX hY (hds.of_same same₁') I J
              (by omega) r hwd)
            ?_ ?_
      |
        refine
          Light.Ends.pieceLast
            (queryAtCore_spec hCore ht hlim hX hY (hds.of_same same₁') I J
              (by omega) r hwd)
            ?_ ?_);
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
    (on_goal -1 => rintro ⟨loc₂, μ₂⟩ ⟨hr, same₂⟩)
  have same₂' : SameOutside μ μ₂ (aWD p b0) (3 * p.L + p.m) := by
    obtain ⟨⟩ := areas p t b0
    exact same₁'.then same₂ fun b hb => ⟨hb, by omega, by omega⟩
  exact ⟨hr, hds.of_same same₂', same₂'⟩

end Proof

end Light.Sec4

end
end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P Light.Sec4.Proc.queryAt)
      (@Option.some.{0} Light.Stmt Light.Sec4.queryAtBody) →
    Light.Sec4.OutDigitsSpec lim P → Light.Sec4.QueryCoreSpec lim P → Light.Sec4.QueryAtSpec lim P := by
  exact @Light.Sec4.queryAt_spec_sourceProof

#print axioms solution
