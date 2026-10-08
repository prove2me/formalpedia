-- Prove2me | solution 1 for Light.Sec2.sharedCallees_of_prefix
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:28:42.910282+00:00
-- url     : https://prove2.me/submissions/c408a727-977e-401f-a94c-02e0524ad334

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
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma10
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma7_8
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Levels
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Counters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_SubsetTable
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSumApsp_Spec_ctrAt_succ
import Theorems.Thm_ThreeSumApsp_Spec_unrank_succ_shape
import Theorems.Thm_ThreeSumApsp_getD_weaveList

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
namespace ThreeSumApsp.Spec.Subsets
end ThreeSumApsp.Spec.Subsets
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

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

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













/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
































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

/-- A weaker conclusion. -/
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩






/-- A branch whose test holds. -/
theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by (((try have := Light.Std.space_le (by assumption)));
                                                   ((try have := Light.Std.const_le (by assumption)));
                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                          ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩

/-- A branch whose test fails. -/
theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by (((try have := Light.Std.space_le (by assumption)));
                                                      ((try have := Light.Std.const_le (by assumption)));
                                                      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                             ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                             (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩

theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
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
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

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

/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
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
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩










/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
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
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

/-! ## Counting loops -/





/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
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
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
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
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

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

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

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

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
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
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

/-- **Counting loops whose body is a block that changes no local variable**, with the locals as a
list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
counts 0 steps in blockCost; for a body that contains one use Ends.forShape. -/
theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                       ((try have := Light.Std.const_le (by assumption)));
                                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first
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
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI

/-- **Counting loops whose body may change scratch variables.**  S j s μ' is the state before round
j, with the values s of the scratch variables and the memory μ'; I j holds of the memory.  The
counter of S j s μ' holds j, and S (j + 1) s μ' is S j s μ' with the counter increased; for a shape
fun j s μ' => ⟨frame [.., j, s], μ'⟩ both are proved by default.  The bound hi gives n, n fits in a
word, and the body keeps the shape and takes at most b steps. -/
theorem Ends.forShape {β : Type} {loc : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt}
    (S : ℕ → β → (ℕ → ℤ) → State) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (s₀ : β) (start : I 0 μ)
    (round : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body (S j s μ') b fun σ' => ∃ s' μ'', σ' = S j s' μ'' ∧ I (j + 1) μ'')
    (done : ∀ (s : β) (μ' : ℕ → ℤ), I n μ' → Q (S n s μ'))
    (first : (⟨Function.update loc i 0, μ⟩ : State) = S 0 s₀ μ := by
      first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (bound : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim (S j s μ') n := by
      intros; (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (counter : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), (S j s μ').loc i = j := by intros; simp)
    (next : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ),
      (⟨Function.update (S j s μ').loc i ((j : ℤ) + 1), (S j s μ').mem⟩ : State) =
        S (j + 1) s μ' := by
      intros; first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
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
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ' => ∃ s μ', σ' = S j s μ' ∧ I j μ') n b ⟨s₀, μ, first, start⟩ ?_ ?_ ?_
    hn hT
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    refine (round j s μ' hj hI).mono le_rfl ?_
    rintro _ ⟨s', μ'', rfl, hI'⟩
    exact ⟨counter j s' μ'', s', μ'', next j s' μ'', hI'⟩
  · rintro _ - ⟨s, μ', rfl, hI⟩
    exact done s μ' hI
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    exact bound j s μ' hj hI

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

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR

/-- A specification whose time is a constant times a shape holds for every larger constant. -/
theorem Meets.mono_const {c c' S : ℕ} (h : Meets lim P p d vals μ (c * S) R) (hc : c ≤ c') :
    Meets lim P p d vals μ (c' * S) R :=
  h.mono_time (Nat.mul_le_mul_right _ hc)







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

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl

theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)

/-- Fewer cells are kept. -/
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)











/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]










/-- Writing `j ≤ n` cells from `dst` changes no cell outside the `n` cells from `dst`. -/
theorem sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)

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

/-- The next index, if it is in the same row. -/
theorem succ_div_mod_of_lt {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by rw [← Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by rw [hsucc, mul_add_div_of_lt h], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩






/-- After the last index of a row comes the first index of the next row. -/
theorem succ_div_mod_of_eq {n i : ℕ} (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by
  have hn : 0 < n := h ▸ Nat.succ_pos _
  have hsucc : i + 1 = (i / n + 1) * n + 0 := by
    have hdivmod := Nat.div_add_mod' i n
    rw [Nat.succ_mul]
    -- `i = i / n * n + i % n` and `i % n + 1 = n`
    omega
  exact ⟨by rw [hsucc, mul_add_div_of_lt hn], by rw [hsucc, Nat.mul_add_mod_of_lt hn]⟩

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





















/-- Entry `i < l.length` of `l.map f`, whatever the two defaults. Mathlib's `List.getD_map` is for
all `i`, with the default `f d`. -/
theorem getD_map_of_lt (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getD_eq_getElem _ _ hi,
    List.getElem_map]






















/-- The first `i + 1` entries are the first `i` entries and entry `i`. -/
theorem take_succ_getD (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_add_one, List.getD_eq_getElem l d hi, List.getElem?_eq_getElem hi,
    Option.toList_some]

/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/

/-- A count among the first `i + 1` entries, from the count among the first `i` and entry `i`. -/
theorem count_take_succ [DecidableEq α] (l : List α) (x : α) {i : ℕ}
    (hi : i < l.length) :
    (l.take (i + 1)).count x = (l.take i).count x + if l[i] = x then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi, List.count_append, List.count_singleton]
  simp

/-- A count among the first `i + 1` entries, with entry `i` read by `getD`. -/
theorem count_take_succ_getD [DecidableEq α] (l : List α) (x : α) {i : ℕ} (hi : i < l.length)
    (d : α) :
    (l.take (i + 1)).count x = (l.take i).count x + if l.getD i d = x then 1 else 0 := by
  rw [List.count_take_succ l x hi, List.getD_eq_getElem l d hi]

/-- If entry `i < l.length` is `x`, then `x` occurs less often before place `i` than in the whole
list. -/
theorem count_take_lt [DecidableEq α] {l : List α} {i : ℕ} {x : α} (hi : i < l.length) (d : α)
    (hx : l.getD i d = x) : (l.take i).count x < l.count x := by
  have hle : (l.take (i + 1)).count x ≤ l.count x := (List.take_sublist _ _).count_le _
  rw [count_take_succ_getD l x hi d, if_pos hx] at hle
  omega




































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












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi









theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega









/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_53226_0 apspMacro_53226_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_53226_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_53226_2 apspMacro_53226_0 (by omega)));
                                                                                                  (revert apspMacro_53226_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_53226_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_53226_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_53226_3 apspMacro_53226_0 (by omega)));
                                                                                                  (revert apspMacro_53226_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_53226_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_53226_4 apspMacro_53226_0 (by omega)));
                                                                                                  (revert apspMacro_53226_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩























theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

theorem SameOutside2.refl {m : ℕ} : SameOutside2 μ μ a n b m := SameOn.refl







/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)




/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]






















/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_54655_0 apspMacro_54655_1);
                                                    (first
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_54655_2));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_54655_2 apspMacro_54655_0 (by omega)));
                                                                    (revert apspMacro_54655_2)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((simp [] at apspMacro_54655_1);
                                                          (((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_54655_3));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_54655_3 apspMacro_54655_0 (by omega)));
                                                                    (revert apspMacro_54655_3)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_54655_4));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_54655_4 apspMacro_54655_0 (by omega)));
                                                                    (revert apspMacro_54655_4)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (fail
                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                        its condition K x does not follow from the hypotheses."))))) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)










/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j






/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n k e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => hlow b (by omega)
















end Light

end
end

section


/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}












/-- **The rule for a pass.**  The locals x and y hold the length n and the address dst.  In round j
the locals are the given ones with j in the counter, and the memory is `wrote μ dst f j`; there the
expression e has to be safe and have the value f j. -/
theorem Ends.pass {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by first
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
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm
    (fun j μ' hj hμ' => Ends.block ?round le_rfl)
    (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
  -- Round j: dst[j] := e.
  subst hμ'
  obtain ⟨hs, hv⟩ := round j hj
  have qc : Function.update loc c (j : ℤ) c = j := Function.update_self ..
  have qy : Function.update loc c (j : ℤ) y = dst := by rw [Function.update_of_ne hy, haddr]
  refine ⟨⟨?_, hs, ?_⟩, rfl, ?_⟩
  · simp only [Expr.Safe, Expr.val, Op.eval, qc, qy, true_and, abs_le]
    omega
  · simp only [Expr.val, Op.eval, qc, qy, Limits.Addr]
    omega
  · simp only [Stmt.after, Expr.val, Op.eval, qc, qy, hv, toNat_natCast_add_natCast, wrote_succ]

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

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable









end PowTable

open PowTable





















/-- The body of powTable writes the powers of b and changes nothing else, whatever its local
variables hold apart from the three arguments. -/
theorem powTable_ends {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by
  have h1 : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  -- p := 1
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
            -- for j < L
            
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
  -- for j < L
  refine Ends.for (Filled μ dst L b t) L powTableRound.blockCost ?start ?round ?done ?bound
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      powTableRound]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [powTableRound] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))))
  case start => exact ⟨μ, by simp [update_frame_setLocal], fun i hi => absurd hi (by omega), .refl⟩
  case bound =>
    rintro j _ - - ⟨μ', rfl, -⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
  case done =>
    rintro _ - ⟨μ', rfl, powers, same⟩
    exact ⟨fun i hi => by rw [getElem_powList]; exact powers i (by simpa using hi), same⟩
  case round =>
    rintro j _ hj - ⟨μ', rfl, powers, same⟩
    have hfits : (b : ℤ) ^ (j + 1) ≤ lim.word := by exact_mod_cast hpow (j + 1) (by omega)
    have hnonneg : 0 ≤ (b : ℤ) ^ (j + 1) := by positivity
    unfold powTableRound
    -- dst[j] := p
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
          Light.Ends.storeToThen (dst + j)
            (b ^ j : ℕ)
              -- p := p * b
              
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
    -- p := p * b
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (b ^ (j + 1) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  ← pow_succ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [← pow_succ] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ← pow_succ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp, Function.update μ' (dst + j) (b ^ j : ℕ), by simp [update_frame_setLocal],
      fun i hi => ?_, by ((try refine Light.SameOn.cell ?_); (intro apspMacro_60096_0 apspMacro_60096_1);
                           (first
                             |
                               ((((repeat
                                         (((with_reducible
                                                 rename Light.SameOn _ _ _ => apspMacro_60096_2));
                                           ((try
                                                 have :=
                                                   apspMacro_60096_2 apspMacro_60096_0 (by omega)));
                                           (revert apspMacro_60096_2)));
                                     (intros);
                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                 (omega))
                             |
                               ((simp [] at apspMacro_60096_1);
                                 (((repeat
                                         (((with_reducible
                                                 rename Light.SameOn _ _ _ => apspMacro_60096_3));
                                           ((try
                                                 have :=
                                                   apspMacro_60096_3 apspMacro_60096_0 (by omega)));
                                           (revert apspMacro_60096_3)));
                                     (intros);
                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                 (omega))
                             |
                               ((((repeat
                                         (((with_reducible
                                                 rename Light.SameOn _ _ _ => apspMacro_60096_4));
                                           ((try
                                                 have :=
                                                   apspMacro_60096_4 apspMacro_60096_0 (by omega)));
                                           (revert apspMacro_60096_4)));
                                     (intros);
                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                 (fail
                                     "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                               SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                               its condition K x does not follow from the hypotheses."))))⟩
    obtain hi | rfl := Nat.lt_succ_iff_lt_or_eq.1 hi
    · rw [Function.update_of_ne (by omega)]
      exact powers i hi
    · exact Function.update_self ..











end Light

end
end

section


/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt







end Sqrt














/-- **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is. -/
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
  have hlt : K < (Nat.sqrt K + 1) * (Nat.sqrt K + 1) := Nat.lt_succ_sqrt K
  have hself : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
  refine .of_body hp ?_
  unfold sqrtBody sqrtTime
  -- k := 0; sq := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
          1
            -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
            
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
  -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) (Nat.sqrt K) (by simp) ?round ?done
    le_rfl)
  case round =>
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    -- The test is safe and holds.  sq := sq + 2 k + 3; k := k + 1 is safe and leads to the next
    -- state.
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- the result is k
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (Nat.sqrt K) ?_ ?_ ?_);
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
    exact ⟨rfl, rfl⟩

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

/-- The levels of `Q` in order depend only on the set `Q`. -/
theorem innerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    innerLevel Q' hQ' = innerLevel Q hQ := by
  subst h
  rfl

/-- The levels outside `Q` in order depend only on the set `Q`. -/
theorem outerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    outerLevel Q' hQ' = outerLevel Q hQ := by
  subst h
  rfl

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

/-- At the `k`-th lowest level of a set `Q'` that is equal to `Q`, the string glued along `Q` has
the `k`-th letter of `f`. -/
private theorem glue_innerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin m) : glue Q hQ f g (innerLevel Q' hQ' k) = f k := by
  rw [innerLevel_congr Q hQ h, glue_innerLevel]

/-- At the `k`-th lowest level outside a set `Q'` that is equal to `Q`, the string glued along `Q`
has the `k`-th letter of `g`. -/
private theorem glue_outerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin (L - m)) :
    glue Q hQ f g (outerLevel Q' hQ' k) = g k := by
  rw [outerLevel_congr Q hQ h, glue_outerLevel]

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

/-- Let every inner letter `s` be `inner i` for its index `i = innerIndex s`, and every outer letter
be `outer o` for its index `o = outerIndex s`. Then a string whose inner letters are at the levels
of `Q` is rebuilt by gluing the letters `inner i` and `outer o` for the indices of its letters. -/
theorem glue_index {I O : Type*} {inner : I → α} {outer : O → α} {innerIndex : α → I}
    {outerIndex : α → O} (hI : ∀ s, IsInner s → inner (innerIndex s) = s)
    (hO : ∀ s, ¬ IsInner s → outer (outerIndex s) = s) {u : Fin L → α}
    (hu : (univ.filter fun ℓ => IsInner (u ℓ)) = Q) :
    u = glue Q hQ (fun k => inner (innerIndex (u (innerLevel Q hQ k))))
      (fun k => outer (outerIndex (u (outerLevel Q hQ k)))) := by
  obtain ⟨hin, hout⟩ := (filter_eq_iff_forall_level Q hQ).mp hu
  exact (eq_glue_iff Q hQ).mpr ⟨fun k => (hI _ (hin k)).symm, fun k => (hO _ (hout k)).symm⟩

/-! ### Left, right and output strings with a given inner set, outer part and inner part -/















/-- The inner set of `leftStrOf Q hQ r π` is `Q`. -/
@[simp]
theorem innerSetL_leftStrOf (r : OuterStr L m) (π : InnerStr m) :
    innerSetL (leftStrOf Q hQ r π) = Q :=
  filter_glue Q hQ LeftVar.IsInner (fun _ => trivial) fun _ => id

/-- The inner set of `rightStrOf Q hQ π c` is `Q`. -/
@[simp]
theorem innerSetR_rightStrOf (π : InnerStr m) (c : OuterStr L m) :
    innerSetR (rightStrOf Q hQ π c) = Q :=
  filter_glue Q hQ RightVar.IsInner (fun _ => trivial) fun _ => id






/-- The outer part of `leftStrOf Q hQ r π` is `r`. -/
@[simp]
theorem outerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : outerPartL (leftStrOf Q hQ r π) h = r :=
  funext fun k => congrArg LeftVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `leftStrOf Q hQ r π` is `π`. -/
@[simp]
theorem innerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : innerPartL (leftStrOf Q hQ r π) h = π :=
  funext fun k => congrArg LeftVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `rightStrOf Q hQ π c` is `π`. -/
@[simp]
theorem innerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : innerPartR (rightStrOf Q hQ π c) h = π :=
  funext fun k => congrArg RightVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The outer part of `rightStrOf Q hQ π c` is `c`. -/
@[simp]
theorem outerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : outerPartR (rightStrOf Q hQ π c) h = c :=
  funext fun k => congrArg RightVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)



















variable {Q}

/-- A left string with inner set `Q` is the string `leftStrOf` of its outer part and its inner
part. -/
theorem leftStr_eq_leftStrOf {u : LeftStr L} (hu : innerSetL u = Q) (h : (innerSetL u).card = m) :
    u = leftStrOf Q hQ (outerPartL u h) (innerPartL u h) := by
  subst hu
  refine glue_index _ h LeftVar.IsInner (inner := fun π : Fin 2 × Fin 2 => .p π.1 π.2) ?_ ?_ rfl
  · rintro (i | ⟨i, j⟩) hs
    exacts [hs.elim, rfl]
  · rintro (i | ⟨i, j⟩) hs
    exacts [rfl, (hs trivial).elim]

/-- A right string with inner set `Q` is the string `rightStrOf` of its inner part and its outer
part. -/
theorem rightStr_eq_rightStrOf {v : RightStr L} (hv : innerSetR v = Q)
    (h : (innerSetR v).card = m) : v = rightStrOf Q hQ (innerPartR v h) (outerPartR v h) := by
  subst hv
  refine glue_index _ h RightVar.IsInner (inner := fun π : Fin 2 × Fin 2 => .q π.1 π.2) ?_ ?_ rfl
  · rintro (j | ⟨i, j⟩) ht
    exacts [ht.elim, rfl]
  · rintro (j | ⟨i, j⟩) ht
    exacts [rfl, (ht trivial).elim]













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














namespace Par
variable (p : Par)

theorem one_le_T : 1 ≤ p.T := Nat.one_le_pow _ _ (by omega)



























end Par











end Light.Sec2

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









/-- A sum over the strings of length `L + 1` is a sum over the first variable `s` and the rest `u'`
of the string `s u'`. -/
private theorem sum_strings_succ {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℤ) :
    ∑ u, f u = ∑ s, ∑ u', f (Fin.cons s u') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun _ => rfl).symm


























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

/-- The entry of the left input array at the string with inner set `Q`, outer part `r` and inner
part `π` is `X_Q[r, π]`. -/
@[simp]
theorem arrayL_leftStrOf {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (r : OuterStr L m) (π : InnerStr m) :
    arrayL m X (leftStrOf Q hQ r π) = X Q r π := by
  have h : (innerSetL (leftStrOf Q hQ r π)).card = m := by rw [innerSetL_leftStrOf, hQ]
  rw [arrayL, dif_pos h, outerPartL_leftStrOf, innerPartL_leftStrOf, innerSetL_leftStrOf]

/-- The entry of the right input array at the string with inner set `Q`, inner part `π` and outer
part `c` is `Y_Q[π, c]`. -/
@[simp]
theorem arrayR_rightStrOf {L m : ℕ} (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (π : InnerStr m) (c : OuterStr L m) :
    arrayR m Y (rightStrOf Q hQ π c) = Y Q π c := by
  have h : (innerSetR (rightStrOf Q hQ π c)).card = m := by rw [innerSetR_rightStrOf, hQ]
  rw [arrayR, dif_pos h, innerPartR_rightStrOf, outerPartR_rightStrOf, innerSetR_rightStrOf]

/-! ### The proof of Lemma 9 -/



















































































































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

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `X_Q`. -/
theorem bandFamilyL_eq_zero {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyL lay X β Q = 0 :=
  sum_eq_zero fun gh _ => if_neg (hQ gh)

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `Y_Q`. -/
theorem bandFamilyR_eq_zero {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyR lay Y β Q = 0 :=
  sum_eq_zero fun gh _ => if_neg (hQ gh)

/-! ### One run of `Full` for each tile -/

























































/-! ### The output string of a position -/



























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
















/-- The code of the digit `s` followed by the string `d`. -/
theorem code_cons (b : ℕ) {n : ℕ} (s : ℕ) (d : Fin n → ℕ) :
    code b (Fin.cons s d : Fin (n + 1) → ℕ) = s * b ^ n + code b d := by
  rw [code, Fin.cons_zero, Fin.tail_cons]

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






/-- One more digit at the end multiplies the value by `b` and adds the digit. -/
theorem ofDigitList_append_singleton (b : ℕ) (l : List ℕ) (x : ℕ) :
    ofDigitList b (l ++ [x]) = ofDigitList b l * b + x := by
  simp [ofDigitList]

/-- The value of the first `i + 1` digits, from the value of the first `i` digits. -/
theorem ofDigitList_take_succ (b : ℕ) (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    ofDigitList b (l.take (i + 1)) = ofDigitList b (l.take i) * b + l.getD i 0 := by
  rw [List.take_succ_getD l hi 0, ofDigitList_append_singleton]

/-- The value of a list of digits is the code of the list, read as a string. -/
theorem ofDigitList_eq_code (b : ℕ) (l : List ℕ) :
    ofDigitList b l = code b fun ℓ : Fin l.length => l[(ℓ : ℕ)] := by
  rw [code_eq_ofDigitList, List.ofFn_getElem]

/-- A number with `n` digits below `b` is below `b^n`. -/
theorem ofDigitList_lt {b : ℕ} (l : List ℕ) (hd : ∀ d ∈ l, d < b) :
    ofDigitList b l < b ^ l.length := by
  rw [ofDigitList_eq_code]
  exact code_lt fun ℓ => hd _ (List.getElem_mem ℓ.isLt)













/-! ## Strings over a numbered alphabet -/

variable {α : Type} {b : ℕ} (e : α ≃ Fin b)









/-- The code of the letter `s` followed by the string `u'`. -/
theorem codeStr_cons {n : ℕ} (s : α) (u' : Fin n → α) :
    codeStr e (Fin.cons s u' : Fin (n + 1) → α) = e s * b ^ n + codeStr e u' := by
  rw [codeStr, codeStr, ← code_cons]
  congr 1
  funext ℓ
  refine Fin.cases ?_ (fun k => ?_) ℓ <;> simp

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

/-- Coding undoes decoding, for a number below `b^n`. -/
theorem codeStr_decodeStr [NeZero b] {n c : ℕ} (hc : c < b ^ n) :
    codeStr e (decodeStr e n c) = c := by
  simp only [codeStr, decodeStr, Equiv.apply_symm_apply]
  exact code_digit hc







/-- The list of digits of the code of a string. -/
@[simp]
theorem digitList_codeStr {n : ℕ} (u : Fin n → α) :
    digitList b n (codeStr e u) = List.ofFn fun ℓ => (e (u ℓ) : ℕ) :=
  digitList_code fun ℓ => (e (u ℓ)).isLt

/-- The string with the code `s · b^n + c` is the letter with the digit `s` followed by the string
with the code `c`. -/
theorem decodeStr_cons [NeZero b] {n : ℕ} (s : α) {c : ℕ} (hc : c < b ^ n) :
    decodeStr e (n + 1) (e s * b ^ n + c) = Fin.cons s (decodeStr e n c) := by
  rw [← decodeStr_codeStr e (Fin.cons s (decodeStr e n c)), codeStr_cons,
    codeStr_decodeStr e hc]





/-! ## The list of the digits of a string -/





section

variable {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ}















































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












































































/-- The digit of the term with the digit `t`. -/
theorem termIdx_termOfNat {t : ℕ} (h : t < 10) : ((termIdx (termOfNat t) : Fin 10) : ℕ) = t := by
  rw [termOfNat, dif_pos h]
  exact congrArg Fin.val (termEquiv.apply_symm_apply ⟨t, h⟩)













/-! Applying one of the five bijections gives the digit. -/









@[simp] theorem pairEquiv_apply (p : Fin 2 × Fin 2) : pairEquiv p = pairIdx p := rfl

/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

























/-- The digit of the inner left variable `p_ij` is 3 plus the digit of the pair `(i, j)`. -/
theorem leftIdx_p (i j : Fin 2) : (leftIdx (.p i j) : ℕ) = 3 + pairIdx (i, j) :=
  Nat.add_assoc _ _ _

/-- The digit of the inner right variable `q_ij` is 3 plus the digit of the pair `(i, j)`. -/
theorem rightIdx_q (i j : Fin 2) : (rightIdx (.q i j) : ℕ) = 3 + pairIdx (i, j) :=
  Nat.add_assoc _ _ _

/-! ## The coefficients of the linear forms, as tables -/





















/-- The table of the `φ_λ(s)` has 70 entries. -/
@[simp] theorem length_phiFlat : phiFlat.length = 70 := rfl

/-- The table of the `ψ_λ(t)` has 70 entries. -/
@[simp] theorem length_psiFlat : psiFlat.length = 70 := rfl

/-- The entry number `7 λ + s` of the table, by digits, is the coefficient `φ_λ(s)`. -/
theorem phiFlat_spec (lam : Term) (s : LeftVar) :
    phiFlat.getD (7 * (termIdx lam : ℕ) + (leftIdx s : ℕ)) 0 = phi lam s := by
  revert lam s
  decide

/-- The entry number `7 λ + t` of the table, by digits, is the coefficient `ψ_λ(t)`. -/
theorem psiFlat_spec (lam : Term) (t : RightVar) :
    psiFlat.getD (7 * (termIdx lam : ℕ) + (rightIdx t : ℕ)) 0 = psi lam t := by
  revert lam t
  decide

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

/-- The entry of the list at `c` is 0 if the array is 0 at every string with the code `c`. -/
theorem getD_arrStr_eq_zero {c : ℕ} (h : ∀ u, codeStr e u = c → a u = 0) :
    (arrStr e a).getD c 0 = 0 := by
  rcases Nat.lt_or_ge c (b ^ n) with hlt | hge
  · rw [getD_arrStr_of_lt e a hlt]
    exact h _ (codeStr_decodeStr e hlt)
  · exact List.getD_eq_default _ _ (by rwa [length_arrStr])

end

/-! ## The three kinds of arrays of Section 2 that the programs store -/










/-- The list of an array on the left strings has `7^n` entries. -/
theorem length_arrL {n : ℕ} (a : LeftStr n → ℤ) : (arrL a).length = 7 ^ n :=
  length_arrStr leftEquiv a

/-- The list of an array on the right strings has `7^n` entries. -/
theorem length_arrR {n : ℕ} (b : RightStr n → ℤ) : (arrR b).length = 7 ^ n :=
  length_arrStr rightEquiv b

/-- The list of an array on the leaves has `10^n` entries. -/
theorem length_arrT {n : ℕ} (enc : Leaf n → ℤ) : (arrT enc).length = 10 ^ n :=
  length_arrStr termEquiv enc

/-- The entry at a left string is the entry of the list at its code. -/
theorem getD_arrL {n : ℕ} (a : LeftStr n → ℤ) (u : LeftStr n) : (arrL a).getD (codeL u) 0 = a u :=
  getD_arrStr leftEquiv a u

/-- The entry at a right string is the entry of the list at its code. -/
theorem getD_arrR {n : ℕ} (b : RightStr n → ℤ) (v : RightStr n) :
    (arrR b).getD (codeR v) 0 = b v :=
  getD_arrStr rightEquiv b v






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

























/-- A mask of the enumeration has `L - m` entries `false`. -/
theorem count_false_unrank {L m r : ℕ} (hr : r < L.choose m) :
    (unrank L m r).count false = L - m := by
  have hall := List.count_not_add_count (unrank L m r) true
  rw [count_unrank hr, length_unrank, Bool.not_true] at hall
  omega


























/-! ## Masks and sets of levels -/








/-- The mask of a set of levels has one entry for each level. -/
theorem length_maskOf {L : ℕ} (Q : Finset (Fin L)) : (maskOf Q).length = L := by
  simp [maskOf]

/-- The entry of the mask at a level says whether the level belongs to the set. -/
theorem getD_maskOf {L n : ℕ} (Q : Finset (Fin L)) (hn : n < L) :
    (maskOf Q).getD n false = decide ((⟨n, hn⟩ : Fin L) ∈ Q) := by
  simp [maskOf, hn]


































/-! ## From one mask to the next -/

/-- The first mask: `m` times `true`, then `L - m` times `false`. -/
theorem unrank_zero {L m : ℕ} (hm : m ≤ L) :
    unrank L m 0 = List.replicate m true ++ List.replicate (L - m) false := by
  induction L generalizing m with
  | zero => simp [unrank, Nat.le_zero.mp hm]
  | succ L ih =>
    cases m with
    | zero => simpa [unrank, List.replicate_succ] using ih (Nat.zero_le L)
    | succ m =>
      have hm' : m ≤ L := Nat.le_of_succ_le_succ hm
      simp [unrank, Nat.choose_pos hm', ih hm', List.replicate_succ]































































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

/-- The column with number `k` of a block is indexed by the string with code `k`. -/
private theorem codeOuter_colIdx (k : Fin (N0 L m)) : codeOuter ((stdLayout hmL).colIdx k) = k :=
  codeOuter_rowIdx hmL k














/-- The column with number `k` of `X` is indexed by the string with code `k`. -/
private theorem codeInner_innerIdx (k : Fin (D m)) : codeInner ((stdLayout hmL).innerIdx k) = k :=
  -- The number that `strEquiv` gives to a string is its code, by definition.
  congrArg Fin.val ((strEquiv pairEquiv m).apply_symm_apply k)

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










































end outDigits



















































/-! ## The codes of the left and right strings, and the input arrays of the bands -/






/-- A left or right string has one digit for each level. -/
@[simp] theorem length_gluedDigits (mask : List Bool) (o i : List ℕ) :
    (gluedDigits mask o i).length = mask.length :=
  length_weaveList ..

/-- The digits of a left or right string are below 7. -/
theorem lt_of_mem_gluedDigits {mask : List Bool} {o i : List ℕ} (ho : ∀ x ∈ o, x < 3)
    (hi : ∀ x ∈ i, x < 4) : ∀ d ∈ gluedDigits mask o i, d < 7 := by
  refine lt_of_mem_weaveList (by norm_num) (fun d hd => (ho d hd).trans (by norm_num))
    fun d hd => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
  have hlt := hi x hx
  omega






/-- The code of a left or right string of `L` levels is below `7^L`. -/
theorem gluedCode_lt {L : ℕ} (m : ℕ) {mask : List Bool} (hmask : mask.length = L) (r k : ℕ) :
    gluedCode L m mask r k < 7 ^ L := by
  have hlt := ofDigitList_lt (gluedDigits mask (digitList 3 (L - m) r) (digitList 4 m k))
    (lt_of_mem_gluedDigits (fun _ => lt_of_mem_digitList (by norm_num))
      fun _ => lt_of_mem_digitList (by norm_num))
  rwa [length_gluedDigits, hmask] at hlt

/-- Left and right strings at once: over an alphabet of seven letters in which the outer letter
number `i` has the digit `i` and the inner letter of the pair `p` the digit 3 plus the digit of `p`,
the string glued from the inner letters of `π` and the outer letters of `r` has the code
`gluedCode`. -/
private theorem codeStr_glue {α : Type} (e : α ≃ Fin 7) {inner : Fin 2 × Fin 2 → α}
    {outer : Fin 3 → α} (hinner : ∀ p, (e (inner p) : ℕ) = 3 + pairIdx p)
    (houter : ∀ i, (e (outer i) : ℕ) = i) {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r : OuterStr L m) (π : InnerStr m) :
    codeStr e (glue Q hQ (fun k => inner (π k)) fun k => outer (r k))
      = gluedCode L m (maskOf Q) (codeOuter r) (codeInner π) := by
  rw [gluedCode, gluedDigits, codeOuter, codeInner, digitList_codeStr, digitList_codeStr,
    List.map_ofFn, codeStr, map_glue Q hQ (fun s => ((e s : Fin 7) : ℕ)), code_glue]
  simp only [hinner, houter, pairEquiv_apply, Equiv.refl_apply, Function.comp_def]

/-- The code of the left string with inner set `Q`, outer part `r` and inner part `π`. -/
theorem codeL_leftStrOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (r : OuterStr L m)
    (π : InnerStr m) :
    codeL (leftStrOf Q hQ r π) = gluedCode L m (maskOf Q) (codeOuter r) (codeInner π) :=
  codeStr_glue leftEquiv (inner := fun p => .p p.1 p.2) (fun p => leftIdx_p p.1 p.2)
    (fun _ => rfl) Q hQ r π

/-- The code of the right string with inner set `Q`, inner part `π` and outer part `c`. -/
theorem codeR_rightStrOf {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) (π : InnerStr m)
    (c : OuterStr L m) :
    codeR (rightStrOf Q hQ π c) = gluedCode L m (maskOf Q) (codeOuter c) (codeInner π) :=
  codeStr_glue rightEquiv (inner := fun p => .q p.1 p.2) (fun p => rightIdx_q p.1 p.2)
    (fun _ => rfl) Q hQ c π

section
variable {L m N : ℕ} (hmL : m ≤ L)

/-- `gluedCode` at the subset of the block product `(g, h)`, a row number and a column number is the
code of a left string. -/
private theorem gluedCode_table_left (gh : Fin (K0 L m) × Fin (K0 L m)) (r : Fin (N0 L m))
    (k : Fin (D m)) :
    gluedCode L m (unrank L m (gh.1 * K0 L m + gh.2)) r k
      = codeL (leftStrOf ((stdLayout hmL).table gh) ((stdLayout hmL).table_card gh)
          ((stdLayout hmL).rowIdx r) ((stdLayout hmL).innerIdx k)) := by
  rw [codeL_leftStrOf, codeOuter_rowIdx, codeInner_innerIdx, maskOf_table]

/-- `gluedCode` at the subset of the block product `(g, h)`, a column number of the block and a row
number of `Y` is the code of a right string. -/
private theorem gluedCode_table_right (gh : Fin (K0 L m) × Fin (K0 L m)) (c : Fin (N0 L m))
    (k : Fin (D m)) :
    gluedCode L m (unrank L m (gh.1 * K0 L m + gh.2)) c k
      = codeR (rightStrOf ((stdLayout hmL).table gh) ((stdLayout hmL).table_card gh)
          ((stdLayout hmL).innerIdx k) ((stdLayout hmL).colIdx c)) := by
  rw [codeR_rightStrOf, codeOuter_colIdx, codeInner_innerIdx, maskOf_table]

/-- The input array of a row band, entry by entry: at the code `gluedCode` of the subset of the
block product `(g, h)`, the row `r` of the block and the column `k`, it holds the entry of (the
padded) `X` in row `(β K₀ + g) N₀ + r` and column `k`. -/
theorem bandArrayL_at (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) (g h : Fin (K0 L m))
    (r : Fin (N0 L m)) (k : Fin (D m)) :
    (arrL (bandArrayL (stdLayout hmL) X β)).getD
        (gluedCode L m (unrank L m (g * K0 L m + h)) r k) 0
      = padRows X ((β * K0 L m + g) * N0 L m + r) k := by
  rw [gluedCode_table_left hmL (g, h) r k, getD_arrL, bandArrayL, arrayL_leftStrOf,
    bandFamilyL_table, rowBlock, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The input array of a column band, entry by entry: at the code `gluedCode` of the subset of the
block product `(g, h)`, the column `c` of the block and the row `k`, it holds the entry of (the
padded) `Y` in row `k` and column `(β K₀ + h) N₀ + c`. -/
theorem bandArrayR_at (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) (g h : Fin (K0 L m))
    (c : Fin (N0 L m)) (k : Fin (D m)) :
    (arrR (bandArrayR (stdLayout hmL) Y β)).getD
        (gluedCode L m (unrank L m (g * K0 L m + h)) c k) 0
      = padCols Y k ((β * K0 L m + h) * N0 L m + c) := by
  rw [gluedCode_table_right hmL (g, h) c k, getD_arrR, bandArrayR, arrayR_rightStrOf,
    bandFamilyR_table, colBlock, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end

/-- The input array of a row band is 0 at every left string whose inner set is not in the table. -/
private theorem bandArrayL_apply_eq_zero {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) (u : LeftStr L)
    (hu : ∀ gh r π, u ≠ leftStrOf (lay.table gh) (lay.table_card gh) r π) :
    bandArrayL lay X β u = 0 := by
  rw [bandArrayL, arrayL]
  split_ifs with hcard
  · -- Section 2.3.4: "let X_Q = Y_Q = 0 for the other subsets Q".
    rw [bandFamilyL_eq_zero lay X β fun gh hgh =>
      hu gh _ _ (leftStr_eq_leftStrOf (lay.table_card gh) hgh.symm hcard)]
    rfl
  · rfl

/-- The input array of a column band is 0 at every right string whose inner set is not in the
table. -/
private theorem bandArrayR_apply_eq_zero {L m N : ℕ} (lay : Layout L m)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) (v : RightStr L)
    (hv : ∀ gh π c, v ≠ rightStrOf (lay.table gh) (lay.table_card gh) π c) :
    bandArrayR lay Y β v = 0 := by
  rw [bandArrayR, arrayR]
  split_ifs with hcard
  · -- Section 2.3.4: "let X_Q = Y_Q = 0 for the other subsets Q".
    rw [bandFamilyR_eq_zero lay Y β fun gh hgh =>
      hv gh _ _ (rightStr_eq_rightStrOf (lay.table_card gh) hgh.symm hcard)]
    rfl
  · rfl

/-- The input array of a row band is 0 at every place that is not a code `gluedCode` as in
`bandArrayL_at`. -/
theorem bandArrayL_eq_zero {L m N : ℕ} (hmL : m ≤ L) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β pos : ℕ) (hpos : ∀ (g h : Fin (K0 L m)) (r : Fin (N0 L m)) (k : Fin (D m)),
      pos ≠ gluedCode L m (unrank L m (g * K0 L m + h)) r k) :
    (arrL (bandArrayL (stdLayout hmL) X β)).getD pos 0 = 0 := by
  refine getD_arrStr_eq_zero leftEquiv _ fun u hcode =>
    bandArrayL_apply_eq_zero _ X β u fun gh r π hu =>
      hpos gh.1 gh.2 ((stdLayout hmL).rowIdx.symm r) ((stdLayout hmL).innerIdx.symm π) ?_
  rw [gluedCode_table_left hmL gh, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hu]
  exact hcode.symm

/-- The input array of a column band is 0 at every place that is not a code `gluedCode` as in
`bandArrayR_at`. -/
theorem bandArrayR_eq_zero {L m N : ℕ} (hmL : m ≤ L) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β pos : ℕ) (hpos : ∀ (g h : Fin (K0 L m)) (c : Fin (N0 L m)) (k : Fin (D m)),
      pos ≠ gluedCode L m (unrank L m (g * K0 L m + h)) c k) :
    (arrR (bandArrayR (stdLayout hmL) Y β)).getD pos 0 = 0 := by
  refine getD_arrStr_eq_zero rightEquiv _ fun v hcode =>
    bandArrayR_apply_eq_zero _ Y β v fun gh π c hv =>
      hpos gh.1 gh.2 ((stdLayout hmL).colIdx.symm c) ((stdLayout hmL).innerIdx.symm π) ?_
  rw [gluedCode_table_right hmL gh, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hv]
  exact hcode.symm

end ThreeSumApsp.Spec

end
end

section


/-!
# Sections 2.4.1 and 2.4.2: the encodings, the recursion `Pruned`, and Lemma 10

The encoding of an array is computed by `Full` with the other array left out (`computeEncoding_phi`,
`computeEncoding_psi`).  `Pruned(S)` is `Full` without that phase, and each call computes only the
outputs in the set `S` that is passed to it.  Lemma 10 (`lemma_10`) has three claims.

* Values.  One induction gives a closed form (`Pruned_eq_restrictTo_sum`): at a string of `S`,
  `Pruned` returns the sum, over the leaves contributing to the string, of the product of the two
  numbers looked up at the leaf.  With the encodings of `a` and `b` this sum is `Mult(a, b)` by
  definition (`Lemma10.values`), which is what `Full` returns by Lemma 7
  (`Pruned_eq_restrictTo_Full`).  The paper compares `Pruned` with `Full` level by level instead.
* Leaves visited.  A vertex below the root is called exactly if it contributes to a string of `U`
  (`Pruned.called_iff_root_or`, `Pruned.called_iff`; the step of the induction is
  `Pruned.called_succ`).  For leaves this is `Lemma10.leaves_visited`.  The set passed to a vertex
  consists of the suffixes of these strings (`Pruned.mem_passed_iff`; no later proof uses this).
* Total size.  A set of strings is no larger than its set of leaves, because a string is determined
  by its private leaf (`card_le_card_Leaves`), and the leaves of `Leaves(S)` that begin with
  `λ` are the leaves of `Leaves(S_λ)` with `λ` put in front (`card_Leaves_succ`).  So the
  sets passed at one depth have total size at most `|Leaves(U)|` (`Pruned.sum_card_passed_le`), and
  there are `L + 1` depths (`Lemma10.total_size`).

Which calls `Pruned` makes depends only on the set passed to it, so the second and the third claim
are proved for any two arrays in place of the two encodings.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Section 2.4.1: the encodings -/











/-- At the leaf `τ` the procedure of Section 2.4.1 stores `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`. -/
theorem computeEncoding_eq_encodeWith {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}
    (a : (Fin L → α) → ℤ) (τ : Leaf L) : computeEncoding c L a τ = encodeWith c τ a := by
  induction L with
  | zero => rw [computeEncoding, encodeWith_zero]
  | succ n ih => rw [computeEncoding, ih, ← encodeWith_cons, Fin.cons_self_tail]

/-- The procedure of Section 2.4.1 computes the encoding of `a`. -/
theorem computeEncoding_phi {L : ℕ} (a : LeftStr L → ℤ) : computeEncoding phi L a = encodingL a :=
  funext (computeEncoding_eq_encodeWith phi a)

/-- The procedure of Section 2.4.1 computes the encoding of `b`. -/
theorem computeEncoding_psi {L : ℕ} (b : RightStr L → ℤ) : computeEncoding psi L b = encodingR b :=
  funext (computeEncoding_eq_encodeWith psi b)

/-! ### Section 2.4.2: the sets `S_λ` of step (2) -/





































/-! ### Lemma 10, first claim: the values -/
























































































/-! ### Lemma 10, second claim: the calls that are made and the sets passed to them -/




















































































































































































































































/-! ### Lemma 10, third claim: the total size of the sets passed -/





















































































































































end ThreeSumApsp

end
end

section


/-!
# Theorem 5 in the light language: the map

One file that fixes everything on which two routines have to agree, besides the sizes and the places
of the arrays: the numbers of the procedures, and for every procedure its arguments, what it needs,
what it leaves behind, which cells it may change, and the shape of its running time. A routine is
proved against its own entry; a caller assumes the entries of the routines it calls. So the proof of
a routine does not depend on the proofs of the routines that it calls.

* Routines never contain an address.  They receive scalars and base addresses as arguments.  Only
  the two main routines (Theorem 5 here, the data structure of Section 4) know the places.
* The stages up to the encodings of all bands are shared with Section 4: procedure pShared fills the
  shared block, which starts at an address b0 above the input and the output of the program that
  calls it (the free pointer).
* An entry XSpec lim P c says: in the program P, within the limits lim, procedure number pX does its
  job within c times the shape of its running time (Meets).  The theorem on a routine proves its
  entry for every c from the constant of the routine on, so a caller can assume several entries at
  one constant.
* The entries of encStep, encodeBands, countSort, copy, runTiles and report stand with these
  routines.
* Strings are numbers: a string over an alphabet of b symbols is its code in base b, level 1 most
  significant (namespace Spec).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Vocabulary -/





/-- A cell of a segment of bits. -/
theorem SegB.get {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : SegB μ a l) {q : ℕ} (hq : q < l.length) :
    μ (a + q) = if l.getD q false then 1 else 0 :=
  (Seg.getD h (by rwa [List.length_map]) 0).trans (List.getD_map_of_lt _ hq false 0)

/-! ## The numbers of the procedures

Number 0 is empty.  1 to 25: the shared routines and those of Theorem 5.  26 to 28: the test of the
regime, the brute force, and the solver for all instances.  29 to 39 are not used.  From 40 on:
Section 4. -/


























































/-! ## The entries of the shared routines -/

section Entries

variable (lim : Limits) (P : Program) (c : ℕ)









































































































































/-! ## The shared stage -/

































































/-! ## Theorem 5 -/







































namespace SortWanted






















end SortWanted

















































































































































































end Entries

end Light.Sec2

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































































end ThreeSumApsp

end
end

section


/-!
# The encodings of all bands of one matrix (Section 2.4.1)

Section 2.4.1: "We compute the encodings of the input arrays of all row bands and all column bands
[...], and every tile reads its two encodings from these."  encodeBands does this for one of the two
matrices: for each band β it calls bandArray, which forms the input array of the band at arr, and
encode, which leaves its encoding in the T = 10^L cells from enc + β T.

The loop is treated once, for callees that are described by what they do here (`encodeBands_proc`).
The two entries, for the row bands of X and for the column bands of Y, put in the specifications of
bandArray and encode for their side.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace Bands

































end Bands












/-- The time of the loop is at most the constant cB + cE + 50 times the shape of the entries. -/
theorem encodeBands_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * 10 ^ p.L + 50) + 6
      ≤ (cB + cE + 50) * (p.nB * (p.T + bandArrayShape p) + 1) := by
  have hT : 1 ≤ p.T := Nat.one_le_pow _ _ (by norm_num)
  have hfifty : p.nB * 50 ≤ p.nB * (50 * p.T) := Nat.mul_le_mul_left _ (by omega)
  change p.nB * (cB * bandArrayShape p + cE * p.T + 50) + 6 ≤ _
  calc p.nB * (cB * bandArrayShape p + cE * p.T + 50) + 6
      = p.nB * (cB * bandArrayShape p) + p.nB * (cE * p.T) + p.nB * 50 + 6 := by ring
    _ ≤ p.nB * (cB * bandArrayShape p) + p.nB * (cE * p.T) + p.nB * (50 * p.T) + 6
        + (p.nB * (cB * p.T) + p.nB * ((cE + 50) * bandArrayShape p) + (cB + cE + 44)) := by omega
    _ = (cB + cE + 50) * (p.nB * (p.T + bandArrayShape p) + 1) := by ring

/-! ## The arguments, and what is assumed about them -/































variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : ℕ → ℤ}

/-- **encodeBands**, at the sizes of `p`, for callees described by what they do here: `HB` says that
`bandArray` leaves the list `A β` at `arr`, within `cB bandArrayShape` steps, `HE` that `encode`
turns it into the list `E β` at `enc + β T`, within `cE 10^L` steps; both in any memory that agrees
with `μ` below `enc`.  Then the lists `E β` stand from `enc` on. -/
theorem encodeBands_proc (std : Std lim) (hP : P[pEncodeBands]? = some encodeBandsBody)
    {d side aA sI sK cB cE : ℕ} {A E : ℕ → List ℤ} (pre : BandsPre lim p μ x coefs V)
    (hd : d < lim.depth) (hE : ∀ β, (E β).length = p.T)
    (HB : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc →
      Meets lim P pBandArray (d + 1)
        [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, side, aA, sI, sK, x.mask, x.dig3, x.dig4, x.arr]
        μ' (cB * bandArrayShape p) fun _ μ'' =>
          Seg μ'' x.arr (A β) ∧ SameOutside μ' μ'' x.arr p.S7)
    (HE : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc → Seg μ' x.arr (A β) →
      Meets lim P pEncode (d + 1) [p.L, x.arr, (x.enc + β * p.T : ℕ), x.zs, x.tab, x.p7, x.p10] μ'
        (cE * 10 ^ p.L) fun _ μ'' => Seg μ'' (x.enc + β * p.T) (E β) ∧
          SameOutside2 μ' μ'' (x.enc + β * p.T) (10 ^ p.L) x.zs (7 ^ p.L)) :
    Meets lim P pEncodeBands d (x.vals p side aA sI sK) μ
      ((cB + cE + 50) * (p.nB * (p.T + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, Seg μ' (x.enc + β * p.T) (E β)) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc) := by
  refine .of_body hP (Ends.mono (T := p.nB * (cB * bandArrayShape p + cE * 10 ^ p.L + 50) + 6) ?_
    (encodeBands_time p cB cE) fun _ h => h)
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id std))
  have hT : p.T = 10 ^ p.L := rfl
  have hS7 : p.S7 = 7 ^ p.L := rfl
  have hnB : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  -- for β < nB: the encodings of the bands below β are in place
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β μ' => (∀ β' < β, Seg μ' (x.enc + β' * p.T) (E β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cE * 10 ^ p.L + 42) 0 ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  -- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr)
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
      |
        refine
          Light.Ends.callToThen
            ((HB β hβ μ'
                (by
                  ((try refine Light.SameOn.cell ?_);
                    (intro apspMacro_132353_0 apspMacro_132353_1);
                    (first
                      |
                        ((((repeat
                                  (((with_reducible
                                          rename Light.SameOn _ _ _ =>
                                            apspMacro_132353_2));
                                    ((try
                                          have :=
                                            apspMacro_132353_2 apspMacro_132353_0
                                              (by omega)));
                                    (revert apspMacro_132353_2)));
                              (intros);
                              (try
                                  simp only [Function.update_apply,
                                    Light.wrote] at *)));
                          (omega))
                      |
                        ((simp [] at apspMacro_132353_1);
                          (((repeat
                                  (((with_reducible
                                          rename Light.SameOn _ _ _ =>
                                            apspMacro_132353_3));
                                    ((try
                                          have :=
                                            apspMacro_132353_3 apspMacro_132353_0
                                              (by omega)));
                                    (revert apspMacro_132353_3)));
                              (intros);
                              (try
                                  simp only [Function.update_apply,
                                    Light.wrote] at *)));
                          (omega))
                      |
                        ((((repeat
                                  (((with_reducible
                                          rename Light.SameOn _ _ _ =>
                                            apspMacro_132353_4));
                                    ((try
                                          have :=
                                            apspMacro_132353_4 apspMacro_132353_0
                                              (by omega)));
                                    (revert apspMacro_132353_4)));
                              (intros);
                              (try
                                  simp only [Function.update_apply,
                                    Light.wrote] at *)));
                          (fail
                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                        its condition K x does not follow from the hypotheses."))))))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (HB β hβ μ'
              (by
                ((try refine Light.SameOn.cell ?_);
                  (intro apspMacro_132353_5 apspMacro_132353_6);
                  (first
                    |
                      ((((repeat
                                (((with_reducible
                                        rename Light.SameOn _ _ _ =>
                                          apspMacro_132353_7));
                                  ((try
                                        have :=
                                          apspMacro_132353_7 apspMacro_132353_5
                                            (by omega)));
                                  (revert apspMacro_132353_7)));
                            (intros);
                            (try
                                simp only [Function.update_apply,
                                  Light.wrote] at *)));
                        (omega))
                    |
                      ((simp [] at apspMacro_132353_6);
                        (((repeat
                                (((with_reducible
                                        rename Light.SameOn _ _ _ =>
                                          apspMacro_132353_8));
                                  ((try
                                        have :=
                                          apspMacro_132353_8 apspMacro_132353_5
                                            (by omega)));
                                  (revert apspMacro_132353_8)));
                            (intros);
                            (try
                                simp only [Function.update_apply,
                                  Light.wrote] at *)));
                        (omega))
                    |
                      ((((repeat
                                (((with_reducible
                                        rename Light.SameOn _ _ _ =>
                                          apspMacro_132353_9));
                                  ((try
                                        have :=
                                          apspMacro_132353_9 apspMacro_132353_5
                                            (by omega)));
                                  (revert apspMacro_132353_9)));
                            (intros);
                            (try
                                simp only [Function.update_apply,
                                  Light.wrote] at *)));
                        (fail
                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                      its condition K x does not follow from the hypotheses."))))))
            ?_ ?_ ?_ ?_);
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₁ μ₁
              ⟨hA, same₁⟩
                  -- encode(L, arr, enc + β T, zs, tab, p7, p10)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- encode(L, arr, enc + β T, zs, tab, p7, p10)
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
      |
        refine
          Light.Ends.callToThen
            ((HE β hβ μ₁
                (by
                  ((try refine Light.SameOn.cell ?_);
                    (intro apspMacro_132482_0 apspMacro_132482_1);
                    (first
                      |
                        ((((repeat
                                  (((with_reducible
                                          rename Light.SameOn _ _ _ =>
                                            apspMacro_132482_2));
                                    ((try
                                          have :=
                                            apspMacro_132482_2 apspMacro_132482_0
                                              (by omega)));
                                    (revert apspMacro_132482_2)));
                              (intros);
                              (try
                                  simp only [Function.update_apply,
                                    Light.wrote] at *)));
                          (omega))
                      |
                        ((simp [] at apspMacro_132482_1);
                          (((repeat
                                  (((with_reducible
                                          rename Light.SameOn _ _ _ =>
                                            apspMacro_132482_3));
                                    ((try
                                          have :=
                                            apspMacro_132482_3 apspMacro_132482_0
                                              (by omega)));
                                    (revert apspMacro_132482_3)));
                              (intros);
                              (try
                                  simp only [Function.update_apply,
                                    Light.wrote] at *)));
                          (omega))
                      |
                        ((((repeat
                                  (((with_reducible
                                          rename Light.SameOn _ _ _ =>
                                            apspMacro_132482_4));
                                    ((try
                                          have :=
                                            apspMacro_132482_4 apspMacro_132482_0
                                              (by omega)));
                                    (revert apspMacro_132482_4)));
                              (intros);
                              (try
                                  simp only [Function.update_apply,
                                    Light.wrote] at *)));
                          (fail
                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                        its condition K x does not follow from the hypotheses.")))))
                hA)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (HE β hβ μ₁
              (by
                ((try refine Light.SameOn.cell ?_);
                  (intro apspMacro_132482_5 apspMacro_132482_6);
                  (first
                    |
                      ((((repeat
                                (((with_reducible
                                        rename Light.SameOn _ _ _ =>
                                          apspMacro_132482_7));
                                  ((try
                                        have :=
                                          apspMacro_132482_7 apspMacro_132482_5
                                            (by omega)));
                                  (revert apspMacro_132482_7)));
                            (intros);
                            (try
                                simp only [Function.update_apply,
                                  Light.wrote] at *)));
                        (omega))
                    |
                      ((simp [] at apspMacro_132482_6);
                        (((repeat
                                (((with_reducible
                                        rename Light.SameOn _ _ _ =>
                                          apspMacro_132482_8));
                                  ((try
                                        have :=
                                          apspMacro_132482_8 apspMacro_132482_5
                                            (by omega)));
                                  (revert apspMacro_132482_8)));
                            (intros);
                            (try
                                simp only [Function.update_apply,
                                  Light.wrote] at *)));
                        (omega))
                    |
                      ((((repeat
                                (((with_reducible
                                        rename Light.SameOn _ _ _ =>
                                          apspMacro_132482_9));
                                  ((try
                                        have :=
                                          apspMacro_132482_9 apspMacro_132482_5
                                            (by omega)));
                                  (revert apspMacro_132482_9)));
                            (intros);
                            (try
                                simp only [Function.update_apply,
                                  Light.wrote] at *)));
                        (fail
                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                      its condition K x does not follow from the hypotheses.")))))
              hA)
            ?_ ?_ ?_ ?_);
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₂ μ₂ ⟨hEβ, same₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by ((try refine Light.SameOn.cell ?_);
                                                       (intro apspMacro_132619_0 apspMacro_132619_1);
                                                       (first
                                                         |
                                                           ((((repeat
                                                                     (((with_reducible
                                                                             rename Light.SameOn _ _ _ => apspMacro_132619_2));
                                                                       ((try
                                                                             have :=
                                                                               apspMacro_132619_2 apspMacro_132619_0 (by omega)));
                                                                       (revert apspMacro_132619_2)));
                                                                 (intros);
                                                                 (try simp only [Function.update_apply, Light.wrote] at *)));
                                                             (omega))
                                                         |
                                                           ((simp [] at apspMacro_132619_1);
                                                             (((repeat
                                                                     (((with_reducible
                                                                             rename Light.SameOn _ _ _ => apspMacro_132619_3));
                                                                       ((try
                                                                             have :=
                                                                               apspMacro_132619_3 apspMacro_132619_0 (by omega)));
                                                                       (revert apspMacro_132619_3)));
                                                                 (intros);
                                                                 (try simp only [Function.update_apply, Light.wrote] at *)));
                                                             (omega))
                                                         |
                                                           ((((repeat
                                                                     (((with_reducible
                                                                             rename Light.SameOn _ _ _ => apspMacro_132619_4));
                                                                       ((try
                                                                             have :=
                                                                               apspMacro_132619_4 apspMacro_132619_0 (by omega)));
                                                                       (revert apspMacro_132619_4)));
                                                                 (intros);
                                                                 (try simp only [Function.update_apply, Light.wrote] at *)));
                                                             (fail
                                                                 "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                           SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                           its condition K x does not follow from the hypotheses."))))⟩
  rcases Nat.lt_or_ge β' β with h | h
  · -- The encodings of the earlier bands lie below enc + β T and have not been touched.
    have hβ'T : β' * p.T + p.T ≤ β * p.T := Nat.mul_add_le_mul h le_rfl
    have hlen := hE β'
    exact (hdone β' h).keep
  · obtain rfl : β' = β := by omega
    exact hEβ

/-! ## What is read does not change -/

/-- The tables that bandArray reads, in a memory that agrees below their bound. -/
theorem BandTables.congr_below {p : Par} {μ μ' : ℕ → ℤ} {mask dig3 dig4 e : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hlow : ∀ x < e, μ' x = μ x) :
    BandTables p μ' mask dig3 dig4 e where
  hmask := fun s hs => (h.hmask s hs).congr fun i hi => hlow _ (by
    have hrow : s * p.L + p.L ≤ p.KK * p.L := Nat.mul_add_le_mul hs le_rfl
    have hend := h.mask_le
    simp at hi
    omega)
  hdig3 := fun I hI => (h.hdig3 I hI).congr fun i hi => hlow _ (by
    have hrow : I * p.Lo + p.Lo ≤ p.N * p.Lo := Nat.mul_add_le_mul hI le_rfl
    have hend := h.dig3_le
    simp at hi
    omega)
  hdig4 := fun x hx => (h.hdig4 x hx).congr fun i hi => hlow _ (by
    have hrow : x * p.m + p.m ≤ p.D * p.m := Nat.mul_add_le_mul hx le_rfl
    have hend := h.dig4_le
    simp at hi
    omega)
  mask_le := h.mask_le
  dig3_le := h.dig3_le
  dig4_le := h.dig4_le

/-- The tables also lie below every larger bound. -/
theorem BandTables.mono {p : Par} {μ : ℕ → ℤ} {mask dig3 dig4 e e' : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hle : e ≤ e') : BandTables p μ mask dig3 dig4 e' :=
  { h with
    mask_le := h.mask_le.trans hle
    dig3_le := h.dig3_le.trans hle
    dig4_le := h.dig4_le.trans hle }

/-- The places of the call of encode for the band β, in a memory that agrees with μ below enc. -/
theorem BandsPre.encodePlaces (pre : BandsPre lim p μ x coefs V) {β : ℕ} (hβ : β < p.nB)
    (hlow : ∀ b < x.enc, μ' b = μ b) :
    EncodePlaces lim p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' := by
  (obtain ⟨⟩ := id pre)
  exact
    { n_le := le_rfl
      hp7 := pre.p7.congr fun i hi => hlow _ (by simp at hi; omega)
      hp10 := pre.p10.congr fun i hi => hlow _ (by simp at hi; omega)
      tab_le := by omega
      p7_le := by omega
      p10_le := by omega
      dst_le := by
        have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
        change x.enc + β * p.T + p.T ≤ x.arr
        omega
      src_le := pre.arr_le
      scr_le := pre.zs_le }

/-! ## The two entries -/













/-- **encodeBands** meets this entry, with every constant from cB + cE + 50 on. -/
theorem encodeBandsL_entry (std : Std lim) (hP : P[pEncodeBands]? = some encodeBandsBody)
    {cB cE c : ℕ} (hB : BandArrayLSpec lim P cB) (hE : EncodeLSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsLSpec lim P c := by
  intro p hmL x aX μ X V pre hM hMle hV d hd
  (obtain ⟨⟩ := id pre)
  refine .mono_const ?_ hc
  refine encodeBands_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aX x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_phiFlat
        omega))
      hA (abs_bandArrayL_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _ (by omega)













/-- **encodeBands** meets this entry, with every constant from cB + cE + 50 on. -/
theorem encodeBandsR_entry (std : Std lim) (hP : P[pEncodeBands]? = some encodeBandsBody)
    {cB cE c : ℕ} (hB : BandArrayRSpec lim P cB) (hE : EncodeRSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsRSpec lim P c := by
  intro p hmL x aY μ Y V pre hM hMle hV d hd
  (obtain ⟨⟩ := id pre)
  refine .mono_const ?_ hc
  refine encodeBands_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aY x.mask x.dig3 x.dig4 x.arr μ' Y (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_psiFlat
        omega))
      hA (abs_bandArrayR_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _ (by omega)

end Light.Sec2

end
end

section


/-!
# The input array of a band: what the loops compute

The input array of a band (Sections 2.3.3 and 2.3.4) holds entries of the matrix at the codes of
certain strings and 0 elsewhere.  The table of subsets lists subsets of size m of the L levels:
`Spec.unrank L m s` is the mask of subset number s, and the block product (g, h) of a tile uses
subset number g K₀ + h.  No program text occurs here.  `BandArgs` collects the arguments of
bandArray: the number of a row, the address of a mask and the code of a string are functions of
them.

* The code of a left or right string is computed level by level: `codeUpTo` is the code of the first
  l levels.  One more level appends the next outer digit, or 3 plus the next inner digit
  (`codeUpTo_succ`), and after all levels the code is `Spec.gluedCode` (`codeUpTo_unrank`).
* The numbers that occur are small (`BandArgs.rowNo_lt`, `subsetIndex_lt`, `BandArgs.code_lt`).
* The array is filled in the order of the tuples (g, h, r, k), not of the codes.  `OverwrittenWith`
  says of two memories that cells of the array were overwritten only with the entries of the target
  list, so that a cell that is right stays right.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The code of a string, level by level -/

section code
variable {bs : List Bool} {o i : List ℕ} {l : ℕ}






/-- One more level. -/
theorem codeUpTo_succ (hl : l < bs.length) :
    codeUpTo bs o i (l + 1) = codeUpTo bs o i l * 7 +
      if bs.getD l false then (i.map (3 + ·)).getD ((bs.take l).count true) 0
      else o.getD ((bs.take l).count false) 0 := by
  rw [codeUpTo, ThreeSumApsp.ofDigitList_take_succ 7 _ (by rwa [Spec.length_gluedDigits]),
    Spec.gluedDigits, ThreeSumApsp.getD_weaveList, if_pos hl]
  rfl

/-- The code of l levels is below 7^l. -/
theorem codeUpTo_lt (ho : ∀ x ∈ o, x < 3) (hi : ∀ x ∈ i, x < 4) (hl : l ≤ bs.length) :
    codeUpTo bs o i l < 7 ^ l := by
  have hlt := ThreeSumApsp.ofDigitList_lt ((Spec.gluedDigits bs o i).take l) fun d hd =>
    Spec.lt_of_mem_gluedDigits ho hi d (List.mem_of_mem_take hd)
  rwa [List.length_take, Spec.length_gluedDigits, Nat.min_eq_left hl] at hlt

end code

/-- On the mask of a subset of the table and the digits of a row and a column, the code of all
levels is `Spec.gluedCode`. -/
theorem codeUpTo_unrank (L m s r k : ℕ) :
    codeUpTo (Spec.unrank L m s) (ThreeSumApsp.digitList 3 (L - m) r) (ThreeSumApsp.digitList 4 m k)
        L
      = Spec.gluedCode L m (Spec.unrank L m s) r k := by
  rw [codeUpTo, List.take_of_length_le (by simp [Spec.length_unrank]), Spec.gluedCode]

/-! ## Sizes -/

/-- A band has at most 7^L rows. -/
private theorem bandSize_le (L m : ℕ) : bandSize L m ≤ 7 ^ L := by
  have hK0 : ThreeSumApsp.K0 L m ≤ 2 ^ L := (Nat.sqrt_le_self _).trans (Nat.choose_le_two_pow _ _)
  have hN0 : ThreeSumApsp.N0 L m ≤ 3 ^ L := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  calc bandSize L m ≤ 2 ^ L * 3 ^ L := Nat.mul_le_mul hK0 hN0
    _ = 6 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 7 ^ L := Nat.pow_le_pow_left (by omega) _
























namespace BandArgs
variable (A : BandArgs)
















/-- A code is below `7^L`. -/
theorem code_lt (g h r k : ℕ) : A.code g h r k < A.p.S7 :=
  Spec.gluedCode_lt A.p.m (Spec.length_unrank ..) r k

variable {A}

/-- The numbers of the rows, and of the blocks, of the padded matrix stay small. -/
theorem rowNo_lt {g h r : ℕ} (hβ : A.β < A.p.nB) (hg : g < A.p.K0) (hh : h < A.p.K0)
    (hr : r < A.p.N0) :
    A.rowNo g h r < A.p.N + A.p.S7 ∧ A.blockNo g h * A.p.N0 < A.p.N + A.p.S7 ∧
      A.blockNo g h < A.p.N + A.p.S7 ∧ A.β * A.p.K0 < A.p.N + A.p.S7 := by
  -- row < nB K₀ N₀ ≤ N + K₀ N₀ - 1 < N + 7^L, and the other three numbers are at most the row.
  have hposition : (if A.side = 0 then g else h) < A.p.K0 := by split <;> assumption
  have hblock : A.β * A.p.K0 + A.p.K0 ≤ A.p.nB * A.p.K0 := Nat.mul_add_le_mul hβ le_rfl
  have hrow : A.blockNo g h * A.p.N0 + A.p.N0 ≤ A.p.nB * A.p.K0 * A.p.N0 :=
    Nat.mul_add_le_mul (show A.blockNo g h < A.p.nB * A.p.K0 by unfold blockNo; omega) le_rfl
  have hbands : A.p.nB * A.p.K0 * A.p.N0 = numBands A.p.L A.p.m A.p.N * bandSize A.p.L A.p.m := by
    rw [Nat.mul_assoc]
    rfl
  have hpad : numBands A.p.L A.p.m A.p.N * bandSize A.p.L A.p.m
      ≤ A.p.N + bandSize A.p.L A.p.m - 1 := Nat.div_mul_le_self _ _
  have hsize := bandSize_le A.p.L A.p.m
  have hsize_pos : 0 < bandSize A.p.L A.p.m :=
    Nat.mul_pos (by change 0 < A.p.K0; omega) (N0_pos _ _)
  have hle : A.blockNo g h ≤ A.blockNo g h * A.p.N0 := Nat.le_mul_of_pos_right _ (by omega)
  have hS7 : A.p.S7 = 7 ^ A.p.L := rfl
  have hfirst : A.β * A.p.K0 ≤ A.blockNo g h := Nat.le_add_right ..
  unfold rowNo
  omega

/-- The offset of a row in its block. -/
theorem rowNo_mod (g h : ℕ) {r : ℕ} (hr : r < A.p.N0) : A.rowNo g h r % A.p.N0 = r := by
  unfold rowNo
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]

end BandArgs

/-- g K₀ + h is the number of a subset of the table. -/
theorem subsetIndex_lt (p : Par) {g h : ℕ} (hg : g < p.K0) (hh : h < p.K0) :
    g * p.K0 + h < p.KK ∧ g * p.K0 + h < p.L.choose p.m :=
  ⟨Nat.mul_add_lt_mul hg hh, Spec.tableIndex_lt p.L p.m (⟨g, hg⟩, ⟨h, hh⟩)⟩

/-- `binom(L, m)`, `K₀`, `N₀` and `L` are at most `7^L`. -/
theorem Par.sizes_le_S7 (p : Par) :
    p.L.choose p.m ≤ p.S7 ∧ p.K0 ≤ p.S7 ∧ p.N0 ≤ p.S7 ∧ p.L < p.S7 := by
  have hchoose : p.L.choose p.m ≤ 2 ^ p.L := Nat.choose_le_two_pow _ _
  have hpow : 2 ^ p.L ≤ 7 ^ p.L := Nat.pow_le_pow_left (by omega) _
  have hK0 : p.K0 ≤ p.L.choose p.m := Nat.sqrt_le_self _
  have hN0 : p.N0 ≤ 7 ^ p.L :=
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)).trans (Nat.pow_le_pow_left (by omega) _)
  have hL : p.L < 7 ^ p.L := Nat.lt_pow_self (by omega)
  have hS7 : p.S7 = 7 ^ p.L := rfl
  omega

/-! ## Overwriting with the entries of a target list -/

section ext
variable {T : List ℤ} {arr n : ℕ} {μ μ' μ'' : ℕ → ℤ}






/-- Nothing has been written. -/
theorem OverwrittenWith.refl : OverwrittenWith T arr n μ μ := ⟨.refl, fun _ _ => Or.inl rfl⟩

/-- First some writes, then more. -/
theorem OverwrittenWith.trans (h₁ : OverwrittenWith T arr n μ μ')
    (h₂ : OverwrittenWith T arr n μ' μ'') : OverwrittenWith T arr n μ μ'' := by
  refine ⟨h₁.1.trans h₂.1, fun c hc => ?_⟩
  rcases h₂.2 c hc with h | h
  · exact (h₁.2 c hc).imp h.trans h.trans
  · exact Or.inr h

/-- One write of an entry of the target. -/
theorem OverwrittenWith.write {c : ℕ} (hc : c < n) :
    OverwrittenWith T arr n μ (Function.update μ (arr + c) (T.getD c 0)) := by
  refine ⟨SameOutside.refl.update ⟨by omega, by omega⟩ _, fun x _ => ?_⟩
  by_cases hx : x = c
  · exact Or.inr (hx ▸ Function.update_self ..)
  · exact Or.inl (Function.update_of_ne (by omega) _ _)

/-- A cell that is right stays right. -/
theorem OverwrittenWith.keep (h : OverwrittenWith T arr n μ μ') {c : ℕ} (hc : c < n)
    (hr : μ (arr + c) = T.getD c 0) :
    μ' (arr + c) = T.getD c 0 :=
  (h.2 c hc).elim (·.trans hr) id

end ext

end Light.Sec2

end
end

section


/-!
# The input array of a band (Section 2.3.4)

Section 2.3.3: "a[u] := X_Q[u], b[v] := Y_Q[v] for all the left strings u and the right strings v
whose inner set Q has exactly m elements, and a[u] := 0, b[v] := 0 at every other string"; in
Section 2.3.4, X_Q and Y_Q are the row block and the column block of the block product with subset
Q.  bandArray writes this input array for a row band of X or a column band of Y.  The array is
laid out by the codes of the left (right) strings and filled in the order of the tuples: the
procedure clears the array, and then, for every block product (g, h) of a tile, every row r of the
block and every column k, it computes the code of the string digit by digit and copies one entry of
the matrix.

The proof goes from the inside to the outside, one lemma for the body of each loop and one for the
loop: a level of the code (`bandLevel_spec`, `bandCodeLoop_spec`), an entry (`bandCell_spec`,
`bandColLoop_spec`), a row of a block (`bandRow_spec`, `bandRowLoop_spec`), a block product
(`bandRows_spec`, `bandBlock_spec`, `bandHLoop_spec`, `bandGLoop_spec`), and the whole procedure
(`bandArray_spec`, within the time `bandArray_time`).  The four outer loops keep the same fact about
the memory: cells of the array are overwritten only with entries of the target list
(`OverwrittenWith`), and the cells of the tuples handled so far are right (`Covered`).  So they are
four cases of one lemma, `coverLoop`.  `bandArrayL_entry` and `bandArrayR_entry`, the cases of X and
of Y, are the specifications that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The program -/

namespace Band






































end Band

open Band























































/-! ## The local variables as a list -/



















































variable {lim : Limits} {P : Program} {d : ℕ} {A : BandArgs} {μ₀ μ : ℕ → ℤ} {T : List ℤ}

/-! ## The loop over the levels -/
























section levels
variable {mrow d3 d4 : ℕ} {bs : List Bool} {o i : List ℕ} {g h blk k : ℤ} {R : RowTmp}

/-- **One level** leads from the state after `l` levels to the state after `l + 1` levels.  No cell
changes. -/
theorem bandLevel_spec (ctx : CodeCtx lim μ A.p.L mrow d3 d4 bs o i) {l : ℕ} (hl : l < A.p.L) :
    Ends lim P d bandLevel ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 l l)), μ⟩
      bandLevel.blockCost fun σ' =>
        σ' = ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 (l + 1) l)), μ⟩ := by
  (obtain ⟨⟩ := id ctx.std)
  have hplaces := And.intro ctx.spaceB <| And.intro ctx.spaceO <| And.intro ctx.spaceI <|
    And.intro ctx.space7 <| And.intro ctx.outer ctx.inner
  have hlen : l < bs.length := ctx.length ▸ hl
  have hbit := ctx.segB.get hlen
  have hcode := codeUpTo_succ (o := o) (i := i) hlen
  have hlt := codeUpTo_lt ctx.outer_lt ctx.inner_lt (show l + 1 ≤ bs.length from hlen)
  have hpow : 7 ^ (l + 1) ≤ 7 ^ A.p.L := Nat.pow_le_pow_right (by omega) hl
  have hfalse := List.count_take_succ_getD bs false hlen false
  have htrue := List.count_take_succ_getD bs true hlen false
  unfold bandLevel
  cases hb : bs.getD l false
  · -- A level outside the set: the next outer digit.
    have hroom := List.count_take_lt hlen false hb
    have hcell := ctx.segO.read (ctx.outer ▸ hroom)
    rw [hb] at hbit hcode hfalse htrue
    simp only [Bool.false_eq_true, if_false, if_true] at hbit hcode hfalse htrue
    rw [hcode] at hlt
    generalize o.getD ((bs.take l).count false) 0 = digit at hcell hcode hlt
    refine Ends.iteLast (fun _ => ?_) (fun hc => absurd (by simp [hbit]) hc)
    -- CodeAcc := CodeAcc * 7 + mem[Outer]; Outer := Outer + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (codeUpTo bs o i (l + 1) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcell,
                  hcode]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcell, hcode] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell, hcode] <;> omega)));
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
          Light.Ends.setToThen (d3 + (bs.take (l + 1)).count false : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hfalse]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hfalse] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hfalse] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    simp only [locals, setLocal, htrue, Nat.add_zero]
  · -- A level of the set: 3 plus the next inner digit.
    have hroom := List.count_take_lt hlen false hb
    have hcell := ctx.segI.read (ctx.inner ▸ hroom)
    rw [hb] at hbit hcode hfalse htrue
    simp only [if_true, reduceCtorEq, if_false,
      List.getD_map_of_lt (3 + ·) (ctx.inner ▸ hroom) 0 0] at hbit hcode hfalse htrue
    rw [hcode] at hlt
    generalize i.getD ((bs.take l).count true) 0 = digit at hcell hcode hlt
    refine Ends.iteLast (fun hc => absurd hc (by simp [hbit])) (fun _ => ?_)
    -- CodeAcc := CodeAcc * 7 + 3 + mem[Inner]; Inner := Inner + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (codeUpTo bs o i (l + 1) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcell,
                  hcode]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcell, hcode] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell, hcode] <;> omega)));
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
          Light.Ends.setToThen (d4 + (bs.take (l + 1)).count true : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, htrue]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [htrue] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, htrue] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    simp only [locals, setLocal, hfalse, Nat.add_zero]

/-- **The loop over the levels** leaves the code of the string in the local `CodeAcc` and changes no
cell. -/
theorem bandCodeLoop_spec (ctx : CodeCtx lim μ A.p.L mrow d3 d4 bs o i) {lev₀ : ℤ} {T' : ℕ}
    {Q : State → Prop}
    (done : ∀ c : CellTmp, c.k = k → c.code = (codeUpTo bs o i A.p.L : ℕ) →
      Q ⟨frame (locals A g ⟨h, blk, mrow⟩ R c), μ⟩)
    (hT : 28 * A.p.L + 6 ≤ T') :
    Ends lim P d bandCodeLoop ⟨frame (locals A g ⟨h, blk, mrow⟩ R ⟨k, 0, d3, d4, lev₀⟩), μ⟩ T'
      Q := by
  ((obtain ⟨⟩ := id ctx); (obtain ⟨⟩ := id ctx.std))
  -- for CurLevel < L
  refine Ends.for (fun l σ =>
      σ = ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 l l)), μ⟩) A.p.L
    bandLevel.blockCost ?start ?round ?done ?bound (by omega) (by simp [bandLevel]; omega)
  case start => simp [update_frame_setLocal, locals, codeUpTo, ThreeSumApsp.ofDigitList]
  case done => exact fun _ _ hσ => hσ ▸ done _ rfl rfl
  case bound => exact fun l _ _ _ hσ => hσ ▸ by (((try have := Light.Std.space_le (by assumption)));
                                                      ((try have := Light.Std.const_le (by assumption)));
                                                      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
  case round =>
    rintro l _ hl - rfl
    refine (bandLevel_spec ctx hl).mono le_rfl ?_
    rintro _ rfl
    exact ⟨by simp, by simp [update_frame_setLocal, locals]⟩

end levels

/-! ## The surroundings -/






















/-- A cell that is right stays right. -/
theorem Covered.keep {μ' : ℕ → ℤ} {g h r k : ℕ} (hc : Covered A T μ g h r k)
    (hext : OverwrittenWith T A.arr A.p.S7 μ μ') : Covered A T μ' g h r k :=
  hext.keep (BandArgs.code_lt ..) hc

namespace BandCtx

/-- Inequalities between the numbers: where the tables, the matrix and the array lie, and bounds on
the sizes. -/
theorem places (C : BandCtx lim A μ₀ T) :
    (lim.space : ℤ) ≤ lim.word ∧ 100 ≤ lim.word ∧ A.p.m ≤ A.p.L ∧ A.arr + A.p.S7 ≤ lim.space ∧
      A.aA + A.p.N * A.p.D ≤ A.arr ∧ A.mask + A.p.KK * A.p.L ≤ A.arr ∧
      A.dig3 + A.p.N * A.p.Lo ≤ A.arr ∧ A.dig4 + A.p.D * A.p.m ≤ A.arr ∧
      A.p.N ≤ A.p.N * A.p.D ∧ A.p.L.choose A.p.m ≤ A.p.S7 ∧ A.p.K0 ≤ A.p.S7 ∧ A.p.N0 ≤ A.p.S7 ∧
      A.p.L < A.p.S7 :=
  ⟨C.std.space_le, C.std.const_le, C.hmL, C.space, C.aA_le, C.tabs.mask_le, C.tabs.dig3_le,
    C.tabs.dig4_le, Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)), A.p.sizes_le_S7⟩

/-- What the loop over the levels reads for the tuple (g, h, r, k), in a memory in which only cells
of the array have changed. -/
private theorem codeCtx (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    {g h r k : ℕ} (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (hk : k < A.p.D) :
    CodeCtx lim μ A.p.L (A.maskRow g h)
      (A.dig3 + A.rowNo g h r * A.p.Lo) (A.dig4 + k * A.p.m)
      (Spec.unrank A.p.L A.p.m (g * A.p.K0 + h)) (ThreeSumApsp.digitList 3 (A.p.L - A.p.m) r)
      (ThreeSumApsp.digitList 4 A.p.m k) := by
  have hplaces := C.places
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hdig3 := Nat.mul_add_le_mul hrow (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hLo : A.p.Lo = A.p.L - A.p.m := rfl
  have hS7 : A.p.S7 = 7 ^ A.p.L := rfl
  have hmaskRow : A.maskRow g h = A.mask + (g * A.p.K0 + h) * A.p.L := rfl
  -- The table of digits in base 3 is indexed by the row of the matrix and holds the digits of the
  -- offset of the row in its block, which is r.
  have hdigits := C.tabs.hdig3 _ hrow
  rw [BandArgs.rowNo_mod g h hr] at hdigits
  exact
    { std := C.std
      length := Spec.length_unrank ..
      outer := by rw [Spec.count_false_unrank hchoose, ThreeSumApsp.length_digitList]
      inner := by rw [Spec.count_unrank hchoose, ThreeSumApsp.length_digitList]
      outer_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      inner_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      segB := (C.tabs.hmask _ hKK).keep
      segO := hdigits.keep
      segI := (C.tabs.hdig4 k hk).keep
      spaceB := by omega
      spaceO := by rw [ThreeSumApsp.length_digitList]; omega
      spaceI := by rw [ThreeSumApsp.length_digitList]; omega
      space7 := by omega }

end BandCtx

/-! ## A loop that fills cells -/

/-- **The four loops at once.**  shape z x is the list of the local variables, with z in the counter
and the local variables x of the loops inside.  If round j overwrites cells only with entries of the
target and establishes fact j, which such writes keep, then the loop establishes fact j for all
j < rounds. -/
theorem coverLoop {X : Type} {arr n rounds b cnt T' : ℕ} {hi : Expr} {body : Stmt}
    (shape : ℤ → X → List ℤ) (fact : ℕ → (ℕ → ℤ) → Prop)
    (keep : ∀ j μ' μ'', fact j μ' → OverwrittenWith T arr n μ' μ'' → fact j μ'')
    (round : ∀ j < rounds, ∀ x μ', OverwrittenWith T arr n μ μ' →
      Ends lim P d body ⟨frame (shape j x), μ'⟩ b fun σ' => ∃ x' μ'',
        σ' = ⟨frame (shape j x'), μ''⟩ ∧ OverwrittenWith T arr n μ' μ'' ∧ fact j μ'')
    (z₀ : ℤ) (x₀ : X)
    (hset : ∀ z x z', setLocal (shape z x) cnt z' = shape z' x := by intros; rfl)
    (hat : ∀ z x, frame (shape z x) cnt = z := by intros; rfl)
    (hbound : ∀ z x μ', hi.Gives lim ⟨frame (shape z x), μ'⟩ rounds := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                                            ((try have := Light.Std.const_le (by assumption)));
                                                                                            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hrounds : (rounds : ℤ) ≤ lim.word := by omega)
    (hT : rounds * (hi.cost + b + 7) + hi.cost + 5 ≤ T' := by first
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
    Ends lim P d (.for cnt hi body) ⟨frame (shape z₀ x₀), μ⟩ T' fun σ' => ∃ x μ',
      σ' = ⟨frame (shape rounds x), μ'⟩ ∧ OverwrittenWith T arr n μ μ' ∧
        ∀ j < rounds, fact j μ' := by
  refine Ends.forShape (fun j x μ' => ⟨frame (shape j x), μ'⟩)
    (fun j μ' => OverwrittenWith T arr n μ μ' ∧ ∀ j' < j, fact j' μ') rounds b x₀
    ⟨.refl, fun j' hj' => absurd hj' (by omega)⟩ ?round (fun x μ' h => ⟨x, μ', rfl, h⟩)
    (by simp only [update_frame_setLocal, hset, Nat.cast_zero]) (fun _ _ _ _ _ => hbound _ _ _)
    (fun _ _ _ => hat _ _)
    (fun _ _ _ => by simp only [update_frame_setLocal, hset, Nat.cast_add, Nat.cast_one]) hrounds hT
  rintro j x μ' hj ⟨hext, hcov⟩
  refine (round j hj x μ' hext).mono le_rfl ?_
  rintro _ ⟨x', μ'', rfl, hext', hnew⟩
  refine ⟨x', μ'', rfl, hext.trans hext', fun j' hj' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact keep j' _ _ (hcov j' hj') hext'
  · exact hnew

/-! ## The loop over the columns -/




section cell
variable {g h r k : ℕ}

/-- **One entry**: the code of the string is computed, and the entry of the matrix is copied to its
cell. -/
theorem bandCell_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (hk : k < A.p.D) (c : CellTmp) :
    Ends lim P d bandCell
      ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) { c with k := k }), μ⟩ (tBandCell A.p)
      fun σ' => ∃ c' : CellTmp, σ' =
        ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) { c' with k := k }),
          Function.update μ (A.arr + A.code g h r k) (T.getD (A.code g h r k) 0)⟩ := by
  have hplaces := C.places
  have hdig3 := Nat.mul_add_le_mul hrow (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hidx := C.idx _ hrow k hk
  have hcode := A.code_lt g h r k
  have hval : μ (A.aA + (A.rowNo g h r * A.sI + k * A.sK))
      = T.getD (A.code g h r k) 0 := by
    rw [C.entry g hg h hh r hr k hk, if_pos hrow]
    exact same _ (Or.inl (by omega))
  have ctx := C.codeCtx same hg hh hr hrow hk
  unfold rowTmp
  generalize A.rowNo g h r = row at *
  have houter : (row : ℤ) * ((A.p.L : ℤ) - A.p.m) = ((row * A.p.Lo : ℕ) : ℤ) := by
    rw [Nat.cast_mul, show A.p.Lo = A.p.L - A.p.m from rfl, Nat.cast_sub C.hmL]
  have haddr : ((A.aA : ℤ) + row * A.sI + k * A.sK).toNat = A.aA + (row * A.sI + k * A.sK) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast,
      Nat.add_assoc]
  unfold bandCell tBandCell
  -- CodeAcc := 0; Outer := dig3 + Row (L - m); Inner := dig4 + Col m
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (A.dig3 + row * A.p.Lo : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                houter]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [houter] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, houter] <;> omega)));
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
          (A.dig4 + k * A.p.m : ℕ)
            -- The code.
            
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
  -- The code.
  refine Ends.next _ (bandCodeLoop_spec ctx ?_ le_rfl)
  rintro ⟨_, _, outer, inner, lev⟩ rfl rfl
  rw [show codeUpTo _ _ _ A.p.L = A.code g h r k from codeUpTo_unrank ..]
  -- mem[arr + CodeAcc] := mem[aA + Row sI + Col sK]
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
        Light.Ends.storeToThen (A.arr + A.code g h r k)
          (T.getD (A.code g h r k) 0) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                hval]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr, hval] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hval] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  exact ⟨⟨k, (A.code g h r k : ℕ), outer, inner, lev⟩, rfl⟩




/-- **The loop over the columns** fills the cells of the tuples (g, h, r, k), k < D. -/
theorem bandColLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (c : CellTmp) :
    Ends lim P d bandColLoop ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) c), μ⟩
      (tBandCol A.p) fun σ' => ∃ (c' : CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) c'), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ k < A.p.D, Covered A T μ' g h r k := by
  have hplaces := C.places
  have hD : A.p.D ≤ A.p.N * A.p.D := Nat.le_mul_of_pos_left _ (by omega)
  -- for Col < D
  refine (coverLoop (b := tBandCell A.p) (rounds := A.p.D)
    (shape := fun z (c : CellTmp) => locals A g (blockTmp A g h) (rowTmp A g h r) { c with k := z })
    (fact := fun k μ' => Covered A T μ' g h r k) (keep := fun _ _ _ hc => hc.keep) (round := ?_)
    c.k c (hT := by simp [tBandCol]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨c', μ', hσ, hfacts⟩ => ⟨_, μ', hσ, hfacts⟩
  intro k hk c' μ' hext
  refine (bandCell_spec C (same.trans hext.1) hg hh hr hrow hk c').mono le_rfl ?_
  rintro _ ⟨c'', rfl⟩
  exact ⟨c'', _, rfl, .write (BandArgs.code_lt ..), Function.update_self ..⟩

end cell

/-! ## The loop over the rows of a block -/











section rows
variable {g h r : ℕ}

/-- **One row of a block**: if the row lies in the matrix, the cells of the tuples `(g, h, r, k)`,
`k < D`, are filled. -/
theorem bandRow_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandRow ⟨frame (locals A g (blockTmp A g h) { R with r := r } c), μ⟩
      (tBandRow A.p) fun σ' => ∃ (x : RowTmp × CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmp A g h) { x.1 with r := r } x.2), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ CoveredRow A T μ' g h r := by
  have hplaces := C.places
  have hsmall := BandArgs.rowNo_lt C.β_lt hg hh hr
  have hrowNo : A.rowNo g h r = A.blockNo g h * A.p.N0 + r := rfl
  unfold bandRow tBandRow
  -- Row := BlockIdx N0 + Offset
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (A.rowNo g h r : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hrowNo]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hrowNo] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hrowNo] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if Row < N
  refine Ends.iteLast (fun hc => ?_) fun hc => Ends.skip ?_
  · have hrow : A.rowNo g h r < A.p.N := by simp at hc; omega
    refine (bandColLoop_spec C same hg hh hr hrow c).mono (by simp) ?_
    rintro _ ⟨c', μ', rfl, hext, hcov⟩
    exact ⟨(rowTmp A g h r, c'), μ', rfl, hext, fun _ => hcov⟩
  · exact ⟨(rowTmp A g h r, c), μ, rfl, .refl,
      fun hrow => absurd hrow (by simp at hc; omega)⟩

/-- **The loop over the rows of a block** fills the cells of the tuples `(g, h, r, k)`, `r < N₀`,
whose row lies in the matrix. -/
theorem bandRowLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandRowLoop ⟨frame (locals A g (blockTmp A g h) R c), μ⟩ (tBandRows A.p)
      fun σ' => ∃ (x : RowTmp × CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmp A g h) x.1 x.2), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  -- for Offset < N0
  exact (coverLoop (b := tBandRow A.p) (rounds := A.p.N0)
    (shape := fun z (x : RowTmp × CellTmp) =>
      locals A g (blockTmp A g h) { x.1 with r := z } x.2)
    (fact := fun r μ' => CoveredRow A T μ' g h r)
    (keep := fun _ _ _ hc hext hrow k hk => (hc hrow k hk).keep hext)
    (round := fun r hr x μ' hext => bandRow_spec C (same.trans hext.1) hg hh hr x.1 x.2)
    R.r (R, c) (hT := by simp [tBandRows]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨x, μ', hσ, hfacts⟩ => ⟨(_, x.2), μ', hσ, hfacts⟩

end rows

/-! ## The loops over h and g -/










section blocks
variable {g h : ℕ}

/-- **The rows of the block product (g, h)**, once the number of the block is known. -/
theorem bandRows_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (mrow : ℤ) (R : RowTmp) (c : CellTmp) {T' : ℕ}
    (hT : tBandRows A.p + 10 ≤ T') :
    Ends lim P d bandRows
      ⟨frame (locals A g ⟨h, (A.blockNo g h : ℕ), mrow⟩ R c), μ⟩ T'
      fun σ' => ∃ (x : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g { x.block with h := h } x.row x.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  -- The address of the mask fits in a word.
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hprod : (((g * A.p.K0 + h) * A.p.L : ℕ) : ℤ) = ((g : ℤ) * A.p.K0 + h) * A.p.L := by
    push_cast
    rfl
  -- MaskRow := mask + (g K0 + h) L
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (A.maskRow g h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                BandArgs.maskRow]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [BandArgs.maskRow] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, BandArgs.maskRow] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine (bandRowLoop_spec C same hg hh R c).mono (by simp; omega) ?_
  rintro _ ⟨x, μ', rfl, hfacts⟩
  exact ⟨⟨blockTmp A g h, x.1, x.2⟩, μ', rfl, hfacts⟩

/-- **One block product**: the number of the block is formed, and the cells of the tuples
`(g, h, r, k)` whose row lies in the matrix are filled. -/
theorem bandBlock_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (H : BlockTmp) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandBlock ⟨frame (locals A g { H with h := h } R c), μ⟩ (tBandBlock A.p)
      fun σ' => ∃ (x : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g { x.block with h := h } x.row x.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  have hsmall := BandArgs.rowNo_lt C.β_lt hg hh (N0_pos A.p.L A.p.m)
  have hrows := fun T' hT' => bandRows_spec (P := P) (d := d) (T' := T') C same hg hh H.mrow R c hT'
  unfold bandBlock tBandBlock
  -- if side = 0 then BlockIdx := β K0 + g else BlockIdx := β K0 + h
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · have hside : A.side = 0 := by simpa using hc
    exact Ends.setToThen _ (hrows _ (by simp))
      (by simp [abs_le, BandArgs.blockNo, hside] at hsmall ⊢; omega)
  · have hside : ¬ A.side = 0 := by simpa using hc
    exact Ends.setToThen _ (hrows _ (by simp))
      (by simp [abs_le, BandArgs.blockNo, hside] at hsmall ⊢; omega)

/-- **The loop over `h`** fills the cells of the tuples `(g, h, r, k)`, `h < K₀`, whose row lies in
the matrix. -/
theorem bandHLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (x : InnerTmp) :
    Ends lim P d bandHLoop ⟨frame (locals A g x.block x.row x.cell), μ⟩ (tBandH A.p)
      fun σ' => ∃ (x' : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g x'.block x'.row x'.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧
        ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  -- for PosH < K0
  exact (coverLoop (b := tBandBlock A.p) (rounds := A.p.K0)
    (shape := fun z (x : InnerTmp) =>
      locals A g { x.block with h := z } x.row x.cell)
    (fact := fun h μ' => ∀ r < A.p.N0, CoveredRow A T μ' g h r)
    (keep := fun _ _ _ hc hext r hr hrow k hk => (hc r hr hrow k hk).keep hext)
    (round := fun h hh x μ' hext => bandBlock_spec C (same.trans hext.1) hg hh x.block x.row x.cell)
    x.block.h x (hT := by simp [tBandH]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨x', μ', hσ, hfacts⟩ => ⟨⟨_, x'.row, x'.cell⟩, μ', hσ, hfacts⟩

/-- **The loop over `g`** fills the cells of all tuples `(g, h, r, k)` whose row lies in the
matrix. -/
theorem bandGLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7) (g₀ : ℤ)
    (x : InnerTmp) :
    Ends lim P d bandGLoop ⟨frame (locals A g₀ x.block x.row x.cell), μ⟩ (tBandG A.p)
      fun σ' => OverwrittenWith T A.arr A.p.S7 μ σ'.mem ∧
        ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRow A T σ'.mem g h r := by
  have hplaces := C.places
  -- for PosG < K0
  refine (coverLoop (b := tBandH A.p) (rounds := A.p.K0)
    (shape := fun z (x : InnerTmp) => locals A z x.block x.row x.cell)
    (fact := fun g μ' => ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRow A T μ' g h r)
    (keep := fun _ _ _ hc hext h hh r hr hrow k hk => (hc h hh r hr hrow k hk).keep hext)
    (round := fun g hg x μ' hext => bandHLoop_spec C (same.trans hext.1) hg x)
    g₀ x (hT := by simp [tBandG]; ring_nf; omega)).mono le_rfl ?_
  rintro _ ⟨x', μ', rfl, hfacts⟩
  exact hfacts

end blocks

/-! ## The whole procedure -/

/-- The time of the whole procedure is within the bound that its callers assume. -/
private theorem bandArray_time (p : Par) :
    p.S7 * 13 + 6 + tBandG p ≤ cBandArray * bandArrayShape p := by
  have hD : 1 ≤ p.D := Nat.pow_pos (by omega)
  have hN0 : 1 ≤ p.N0 := N0_pos _ _
  have hK0 : p.K0 ≤ p.K0 * p.K0 := Nat.le_mul_self _
  have hKK : p.K0 * p.K0 ≤ p.K0 * p.K0 * p.N0 := Nat.le_mul_of_pos_right _ hN0
  have hrows : p.K0 * p.K0 * p.N0 ≤ p.K0 * p.K0 * p.N0 * p.D := Nat.le_mul_of_pos_right _ hD
  have htime : tBandG p = 28 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 44 * (p.K0 * p.K0 * p.N0 * p.D)
      + 24 * (p.K0 * p.K0 * p.N0) + 34 * (p.K0 * p.K0) + 14 * p.K0 + 6 := by
    unfold tBandG tBandH tBandBlock tBandRows tBandRow tBandCol tBandCell
    ring
  have hshape : cBandArray * bandArrayShape p = 120 * p.S7
      + 120 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 120 * (p.K0 * p.K0 * p.N0 * p.D) + 120 * p.L
      + 120 := by
    unfold cBandArray bandArrayShape Par.KK
    ring
  omega






/-- **bandArray** writes the list T to the array and changes nothing else. -/
theorem bandArray_spec (C : BandCtx lim A μ₀ T) :
    Ends lim P d bandArrayBody ⟨frame (args A), μ₀⟩ (cBandArray * bandArrayShape A.p) fun σ' =>
      Seg σ'.mem A.arr T ∧ SameOutside μ₀ σ'.mem A.arr A.p.S7 := by
  have hplaces := C.places
  have htime := bandArray_time A.p
  have hcleared : SameOutside μ₀ (wrote μ₀ A.arr (fun _ => 0) A.p.S7) A.arr A.p.S7 :=
    sameOutside_wrote le_rfl
  -- The array is cleared.
  refine Ends.next _ (Ends.pass (x := Cells) (y := Dest) (dst := A.arr) (n := A.p.S7) (fun _ => 0)
    (fun j _ => by (((try have := Light.Std.space_le (by assumption)));
                     ((try have := Light.Std.const_le (by assumption)));
                     (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) ?_ C.std.space_le C.space rfl rfl (hT := le_rfl)) (by simp; omega)
  -- The loops over the tuples (g, h, r, k); the ten local variables of the inner loops start at 0.
  rw [update_frame_setLocal, ← frame_append_zeros _ 10]
  refine (bandGLoop_spec C hcleared A.p.S7 ⟨⟨0, 0, 0⟩, ⟨0, 0⟩, ⟨0, 0, 0, 0, 0⟩⟩).mono
    (by simp; omega) ?_
  rintro ⟨_, μ'⟩ ⟨hext, hcov⟩
  dsimp only at hext hcov ⊢
  refine ⟨fun c hc => ?_, hcleared.trans hext.1⟩
  have hc7 : c < A.p.S7 := C.T_len ▸ hc
  rw [← List.getD_eq_getElem T 0 hc]
  -- A cell whose entry is 0 is right, whether it has been overwritten or not.
  have hzero : T.getD c 0 = 0 → μ' (A.arr + c) = T.getD c 0 := fun h0 =>
    (hext.2 c hc7).elim (fun h => by rw [h, wrote_done hc7, h0]) id
  by_cases hx : ∃ g < A.p.K0, ∃ h < A.p.K0, ∃ r < A.p.N0, ∃ k < A.p.D, c = A.code g h r k
  · obtain ⟨g, hg, h, hh, r, hr, k, hk, rfl⟩ := hx
    by_cases hrow : A.rowNo g h r < A.p.N
    · exact hcov g hg h hh r hr hrow k hk
    · exact hzero (by rw [C.entry g hg h hh r hr k hk, if_neg hrow])
  · exact hzero (C.zero c fun g hg h hh r hr k hk hce => hx ⟨g, hg, h, hh, r, hr, k, hk, hce⟩)

/-! ## What the callers assume -/











/-- **The specification that the callers of bandArray assume, for a row band of X.** -/
theorem bandArrayL_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBody) :
    BandArrayLSpec lim P cBandArray := by
  intro p hmL β aX mask dig3 dig4 arr μ X hsp hX hXle htab hβ d _
  refine ⟨bandArrayBody, hP, bandArray_spec (A := .ofX p β aX mask dig3 dig4 arr)
    { std := std, hmL := hmL, space := hsp, aA_le := hXle, tabs := htab, β_lt := hβ
      T_len := Spec.length_arrL _
      idx := fun row hrow k hk => ?_
      entry := fun g hg h hh r hr k hk => ?_
      zero := fun c hc =>
        Spec.bandArrayL_eq_zero hmL X β c fun g h r k => hc g g.2 h h.2 r r.2 k k.2 }⟩
  · -- The entry (row, k) of X stands at row D + k.
    dsimp only at hrow hk ⊢
    have hroom := Nat.mul_add_le_mul hrow (le_refl p.D)
    omega
  · refine (Spec.bandArrayL_at hmL X β ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩).trans ?_
    change padRows X ((BandArgs.ofX p β aX mask dig3 dig4 arr).rowNo g h r) ⟨k, hk⟩ = _
    generalize (BandArgs.ofX p β aX mask dig3 dig4 arr).rowNo g h r = row
    unfold padRows
    by_cases hrow : row < p.N
    · rw [dif_pos hrow, if_pos hrow, ← hX ⟨_, hrow⟩ ⟨k, hk⟩]
      refine congrArg μ ?_
      change aX + row * p.D + k = aX + (row * p.D + k * 1)
      omega
    · rw [dif_neg hrow, if_neg hrow]

/-- **The specification that the callers of bandArray assume, for a column band of Y.** -/
theorem bandArrayR_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBody) :
    BandArrayRSpec lim P cBandArray := by
  intro p hmL β aY mask dig3 dig4 arr μ Y hsp hY hYle htab hβ d _
  refine ⟨bandArrayBody, hP, bandArray_spec (A := .ofY p β aY mask dig3 dig4 arr)
    { std := std, hmL := hmL, space := hsp, aA_le := by rwa [Nat.mul_comm], tabs := htab
      β_lt := hβ, T_len := Spec.length_arrR _
      idx := fun row hrow k hk => ?_
      entry := fun g hg h hh r hr k hk => ?_
      zero := fun c hc =>
        Spec.bandArrayR_eq_zero hmL Y β c fun g h r k => hc g g.2 h h.2 r r.2 k k.2 }⟩
  · -- The entry (k, row) of Y stands at k N + row.
    dsimp only at hrow hk ⊢
    have hroom := Nat.mul_add_le_mul hk (le_refl p.N)
    rw [Nat.mul_comm p.N p.D]
    omega
  · refine (Spec.bandArrayR_at hmL Y β ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩).trans ?_
    change padCols Y ⟨k, hk⟩ ((BandArgs.ofY p β aY mask dig3 dig4 arr).rowNo g h r) = _
    generalize (BandArgs.ofY p β aY mask dig3 dig4 arr).rowNo g h r = row
    unfold padCols
    by_cases hrow : row < p.N
    · rw [dif_pos hrow, if_pos hrow, ← hY ⟨k, hk⟩ ⟨_, hrow⟩]
      refine congrArg μ ?_
      change aY + k * p.N + row = aY + (row * 1 + k * p.N)
      omega
    · rw [dif_neg hrow, if_neg hrow]

end Light.Sec2

end
end

section


/-!
# One encoding step (step (2) of Full, Section 2.3.1)

"For each term λ of Schönhage's identity, form A_λ := ∑_s φ_λ(s) a_s and B_λ := ∑_t ψ_λ(t) b_t."
The array a is in 7 n consecutive cells at src, slice after slice; the coefficients of all the forms
are in a table at tab, seven for each term; the array A_λ is written to n cells at dst.  B_λ is
formed by the same procedure, from the array b and the table of the coefficients of the ψ_λ.

`encStepVal` is the sum that belongs in a cell, summand by summand.  Its partial sums are small
(`EncStepPre.val_bounds`), and it does not change while the cells of `dst` are written
(`EncStepPre.val_congr`).  `encStepSum_spec` forms one sum, and `encStep_meets` runs through the
cells.
-/

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp

namespace EncStep












end EncStep

open EncStep















/-! ## The sums -/








/-- One more summand. -/
private theorem encStepVal_succ (μ : ℕ → ℤ) (src lam tab n j s : ℕ) :
    encStepVal μ src lam tab n j (s + 1)
      = encStepVal μ src lam tab n j s + μ (tab + 7 * lam + s) * μ (src + s * n + j) :=
  Finset.sum_range_succ ..













variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' : ℕ → ℤ} {src dst n lam tab j : ℕ} {V : ℤ}

/-- The product of a coefficient in {-1, 0, 1} and a number of absolute value at most `V`. -/
theorem enc_coef_mul_bound {x y V : ℤ} (hx : -1 ≤ x ∧ x ≤ 1) (hy : -V ≤ y ∧ y ≤ V) :
    -V ≤ x * y ∧ x * y ≤ V := by
  have h : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  rcases h with rfl | rfl | rfl <;> constructor <;> omega

/-- A sum of `s` numbers of absolute value at most `V` is at most `s V` in absolute value. -/
theorem enc_sum_bound {f : ℕ → ℤ} {V : ℤ} (s : ℕ) (h : ∀ i < s, -V ≤ f i ∧ f i ≤ V) :
    -(s * V) ≤ ∑ i ∈ range s, f i ∧ ∑ i ∈ range s, f i ≤ s * V := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hsum := ih fun i hi => h i (by omega)
    have hnew := h s (by omega)
    rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
    omega

namespace EncStepPre

/-- One summand is at most `V` in absolute value. -/
private theorem summand_bounds (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s : ℕ}
    (hs : s < 7) : -V ≤ μ (tab + 7 * lam + s) * μ (src + s * n + j) ∧
      μ (tab + 7 * lam + s) * μ (src + s * n + j) ≤ V := by
  have hval := pre.vals (s * n + j) (Nat.mul_add_lt_mul hs hj)
  rw [← Nat.add_assoc] at hval
  exact enc_coef_mul_bound (pre.coef s hs) hval

/-- The sum of `s` summands is at most `s V` in absolute value. -/
private theorem val_bounds (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s : ℕ}
    (hs : s ≤ 7) :
    -(s * V) ≤ encStepVal μ src lam tab n j s ∧ encStepVal μ src lam tab n j s ≤ s * V :=
  enc_sum_bound s fun _ hi => pre.summand_bounds hj (by omega)

/-- The hypotheses still hold when cells of `dst` have been written. -/
theorem keep (pre : EncStepPre lim μ src dst n lam tab V) (same : SameOutside μ μ' dst n) :
    EncStepPre lim μ' src dst n lam tab V := by
  (obtain ⟨⟩ := id pre)
  exact { pre with
    coef := fun i hi => by rw [same _ (by omega)]; exact pre.coef i hi
    vals := fun i hi => by rw [same _ (by omega)]; exact pre.vals i hi }

/-- The sums do not change when cells of `dst` are written. -/
private theorem val_congr (pre : EncStepPre lim μ src dst n lam tab V)
    (same : SameOutside μ μ' dst n) (hj : j < n) :
    encStepVal μ' src lam tab n j 7 = encStepVal μ src lam tab n j 7 := by
  (obtain ⟨⟩ := id pre)
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi7 : i < 7 := Finset.mem_range.mp hi
  have hlt : i * n + j < 7 * n := Nat.mul_add_lt_mul hi7 hj
  rw [same _ (by omega), same _ (by omega)]

end EncStepPre

/-! ## The program -/

variable {T : ℕ} {Q : State → Prop}

/-- **One sum**: the loop over the seven summands leaves the sum for cell j in the local Acc. -/
theorem encStepSum_spec (pre : EncStepPre lim μ src dst n lam tab V) (hj : j < n) {s₀ : ℤ}
    (done : Q ⟨frame [src, dst, n, lam, tab, j, encStepVal μ src lam tab n j 7, (7 : ℕ)], μ⟩)
    (hT : 202 ≤ T) :
    Ends lim P d encStepSum ⟨frame [src, dst, n, lam, tab, j, 0, s₀], μ⟩ T Q := by
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.std))
  -- for Var < 7
  refine Ends.for (fun s σ => σ =
      ⟨frame [src, dst, n, lam, tab, j, encStepVal μ src lam tab n j s, s], μ⟩) 7
    encStepAdd.blockCost ?start ?round ?done ?bound (by omega) (by simp [encStepAdd]; omega)
  case start => simp [update_frame_setLocal, encStepVal]
  case done => exact fun _ _ h => h ▸ done
  case bound => exact fun s _ _ _ h => h ▸ by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
  case round =>
    rintro s _ hs - rfl
    -- The two cells that are read, and the sizes of the numbers.
    have hlt : s * n + j < 7 * n := Nat.mul_add_lt_mul hs hj
    have hsum := pre.val_bounds hj (show s ≤ 7 by omega)
    have hnew := pre.summand_bounds hj hs
    have hnext := pre.val_bounds hj (show s + 1 ≤ 7 by omega)
    have hsV : ((s + 1 : ℕ) : ℤ) * V ≤ 7 * V := by
      have hV : 0 ≤ V := by have := pre.vals 0 (by omega); omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hV
    have hcoef : ((tab : ℤ) + 7 * lam + s).toNat = tab + 7 * lam + s := by omega
    have hcell : ((src : ℤ) + s * n + j).toNat = src + s * n + j := by
      rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]
    have hprod : ((s * n : ℕ) : ℤ) = s * n := Nat.cast_mul s n
    -- Acc := Acc + tab[7 lam + Var] * src[Var n + Cell]
    unfold encStepAdd
    refine Ends.setTo (encStepVal μ src lam tab n j (s + 1)) ⟨by simp, ?_⟩ ?_
    · simp [update_frame_setLocal]
    · rw [encStepVal_succ] at hnext ⊢
      simp [Limits.Addr, abs_le, hcoef, hcell, -abs_mul]
      omega




/-- **encStep** writes `∑_{s < 7} tab[7 lam + s] · src[s n + j]` to `dst[j]` for all `j < n` and
changes nothing else. -/
theorem encStep_meets {p : ℕ} (hp : P[p]? = some encStepBody)
    (pre : EncStepPre lim μ src dst n lam tab V) :
    Meets lim P p d [src, dst, n, lam, tab] μ (tEncStep n) fun _ μ' =>
      (∀ j < n, μ' (dst + j) = encStepVal μ src lam tab n j 7) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp ?_
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.std))
  -- for Cell < n: the first Cell cells of dst have been written
  refine Ends.forShape
    (fun j (s : ℤ × ℤ) μ' => ⟨frame [src, dst, n, lam, tab, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = wrote μ dst (encStepOut μ src lam tab n) j) n 209 (0, 0) wrote_zero.symm
    ?round ?done (by rw [update_frame_setLocal, ← frame_append_zeros _ 2]; rfl)
    (hT := by simp [tEncStep]; omega)
  case done =>
    rintro s _ rfl
    exact ⟨fun j hj => wrote_done (f := encStepOut μ src lam tab n) hj,
      sameOutside_wrote (f := encStepOut μ src lam tab n) le_rfl⟩
  case round =>
    rintro j s _ hj rfl
    have same : SameOutside μ (wrote μ dst (encStepOut μ src lam tab n) j) dst n :=
      sameOutside_wrote hj.le
    unfold encStepCell
    -- Acc := 0; the sum; mem[dst + Cell] := Acc
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
    refine Ends.next _ (encStepSum_spec (pre.keep same) hj ?_ le_rfl)
    rw [pre.val_congr same hj]
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
          Light.Ends.storeToThen (dst + j) (encStepVal μ src lam tab n j 7) ?_ ?_
            ?_);
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
    exact ⟨(encStepVal μ src lam tab n j 7, (7 : ℕ)), _, rfl, wrote_succ⟩

end Light.Sec2

end
end

section


/-!
# The encoding of an array by the recursion of Section 2.4.1

"To compute it, we run Full with b left out and without step (4)" (Section 2.4.1).  If L = 0 the
leaf stores its number.  Otherwise, for each term λ, step (2) writes A_λ to a scratch area and the
recursive call of step (3) encodes it into the part of the output that belongs to the leaves below
λ.  The language has no division, so the lengths 7^{L-1} and 10^{L-1} of the parts are read from two
tables of powers.

`encIdx` is what `encode` computes, in terms of positions in arrays.  `encode` writes it to the
output within `encTime L = O(10^L)` steps (`encTime_le`), using `scrSize L` scratch cells.  The
proof is by induction on `L`:

* the hypotheses of `encode` at level `L + 1` give those of `encStep` (`EncodePre.toStep`) and,
  after it, those of the recursive call (`EncodePre.toRec`);
* the two calls for the term `λ` fill the part of the output below `λ` (`TermsDone.step`,
  `encodeTerm_spec`);
* `encode_leaf` is the case `L = 0`, `encode_node` the loop over the ten terms, and `encode_spec`
  the induction.
-/

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp

namespace Encode















end Encode

open Encode

















/-! ## What encode computes, how much room and how much time it needs -/













/-- The part of the encoding below the term number lam is the encoding of A_lam. -/
private theorem encIdx_succ (c a : ℕ → ℤ) (L lam : ℕ) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c (L + 1) a (lam * 10 ^ L + i) = encIdx c L (encSlice c a L lam) i := by
  rw [encIdx, Nat.mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi]


















/-- The number of steps is `O(10^L)`.  The two further terms on the left make the induction go
through. -/
theorem encTime_le (L : ℕ) : encTime L + 724 * 7 ^ L + 45 ≤ cEncode * 10 ^ L := by
  unfold cEncode
  induction L with
  | zero => simp [encTime]
  | succ L ih =>
    simp only [encTime, tEncStep, pow_succ]
    omega

/-! ## The hypotheses -/





























variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam : ℕ} {V : ℤ} {a c : ℕ → ℤ}

/-- The layout at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and `scrSize L`. -/
theorem EncodeLayout.places_succ (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) :
    tab + 70 ≤ out ∧ p7 + (L + 1) ≤ out ∧ p10 + (L + 1) ≤ out ∧ out + 10 * 10 ^ L ≤ src ∧
      src + 7 * 7 ^ L ≤ scr ∧ scr + (7 ^ L + scrSize L) ≤ lim.space ∧
      (lim.space : ℤ) ≤ lim.word ∧ (100 : ℤ) ≤ lim.word := by
  simpa only [pow_succ', scrSize] using And.intro lay.tab_le <| And.intro lay.p7_le <|
    And.intro lay.p10_le <| And.intro lay.out_le <| And.intro lay.src_le <|
    And.intro lay.scr_le <| And.intro lay.std.space_le lay.std.const_le

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
private theorem sameOutside2_succ (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  simpa only [pow_succ', scrSize] using h

/-- The layout of the recursive call for the term number `lam`: it reads the first `7^L` cells of
the scratch area, writes the part of the output below the term, and has the rest of the scratch
area. -/
private theorem EncodeLayout.toRec (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) :
    EncodeLayout lim scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 L := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  exact ⟨lay.std, by omega, by omega, by omega, by omega, by omega, by omega⟩

namespace EncodePre

/-- The bound `V` is not negative. -/
private theorem V_nonneg (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) : 0 ≤ V := by
  have := pre.src_bound 0 (by positivity)
  omega

/-- In the course of `encode` at level `L + 1`, the hypotheses of `encStep` hold for every term. -/
private theorem toStep (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    EncStepPre lim μ' src scr (7 ^ L) lam tab V := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hV := pre.V_nonneg
  have hword := pre.word_bound
  have hone : (1 : ℤ) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  rw [pow_succ'] at hword
  push_cast at hword
  exact
    { std := pre.lay.std, tab_le := by omega, src_le := by omega, dst_le := by omega
      coef := fun i hi => by
        rw [Nat.add_assoc, hkept _ (by omega), pre.tabV _ (by omega)]
        exact pre.coef_bound _ (by omega)
      vals := fun i hi => by
        rw [hkept _ (by omega), pre.srcV i (by rw [pow_succ']; omega)]
        exact pre.src_bound i (by rw [pow_succ']; omega)
      word_bound := (mul_le_mul_of_nonneg_right (by omega) hV).trans hword }

/-- After `encStep` has written `A_lam` to the scratch area, the hypotheses of `encode` hold at
level `L` for the recursive call. -/
private theorem toRec (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hlam : lam < 10)
    (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1)))
    (hstep : ∀ j < 7 ^ L, μ₁ (scr + j) = encStepVal μ' src lam tab (7 ^ L) j 7)
    (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) :
    EncodePre lim μ₁ scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 (7 * V) L
      (encSlice c a L lam) c := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hword := pre.word_bound
  have hsrc : ∀ j < 7 * 7 ^ L, μ' (src + j) = a j := fun j hj => by
    rw [hkept _ (by omega)]
    exact pre.srcV j (by rw [pow_succ']; omega)
  have htab : ∀ i < 70, μ' (tab + i) = c i := fun i hi => by
    rw [hkept _ (by omega)]
    exact pre.tabV i hi
  exact
    { lay := pre.lay.toRec hlam
      srcV := fun j hj => by
        rw [hstep j hj]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs7 : s < 7 := Finset.mem_range.mp hs
        rw [Nat.add_assoc tab, htab (7 * lam + s) (by omega), Nat.add_assoc src,
          hsrc _ (Nat.mul_add_lt_mul hs7 hj)]
      src_bound := fun j hj => by
        simpa [encSlice] using enc_sum_bound 7 fun s hs =>
          enc_coef_mul_bound (pre.coef_bound (7 * lam + s) (by omega))
            (pre.src_bound (s * 7 ^ L + j) (by rw [pow_succ']; exact Nat.mul_add_lt_mul hs hj))
      tabV := fun i hi => by rw [same₁ _ (by omega), htab i hi]
      coef_bound := pre.coef_bound
      p7V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p7V i (by omega)]
      p10V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p10V i (by omega)]
      word_bound := by
        rw [pow_succ'] at hword
        push_cast at hword ⊢
        rwa [show (7 : ℤ) ^ L * (7 * V) = 7 * 7 ^ L * V by ring] }

end EncodePre

/-! ## One term -/







/-- The two calls for the term number `lam` fill the part of the output below it. -/
theorem TermsDone.step (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) (hlam : lam < 10)
    (h : TermsDone μ out scr L a c lam μ') (same₁ : SameOutside μ' μ₁ scr (7 ^ L))
    (hpost : EncodePost μ₁ (out + lam * 10 ^ L) (scr + 7 ^ L) L (encSlice c a L lam) c μ₂) :
    TermsDone μ out scr L a c (lam + 1) μ₂ := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  obtain ⟨hdone, same⟩ := h
  obtain ⟨hnew, same₂⟩ := hpost
  have hkept := sameOutside2_succ same
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Nat.succ_mul] at hi
    by_cases hold : i < lam * 10 ^ L
    · -- The parts below the earlier terms are not touched.
      rw [same₂ _ (by omega), same₁ _ (by omega), hdone i hold]
    · -- The part below this term.
      obtain ⟨i, rfl⟩ : ∃ i', i = lam * 10 ^ L + i' := ⟨i - lam * 10 ^ L, by omega⟩
      rw [← Nat.add_assoc, hnew i (by omega), encIdx_succ c a L lam (by omega)]
  · simp only [pow_succ', scrSize]
    clear same
    ((try refine Light.SameOn.cell ?_);
      (intro apspMacro_188331_0 apspMacro_188331_1);
      (first
        |
          ((((repeat
                    (((with_reducible
                            rename Light.SameOn _ _ _ => apspMacro_188331_2));
                      ((try
                            have :=
                              apspMacro_188331_2 apspMacro_188331_0 (by omega)));
                      (revert apspMacro_188331_2)));
                (intros);
                (try simp only [Function.update_apply, Light.wrote] at *)));
            (omega))
        |
          ((simp [] at apspMacro_188331_1);
            (((repeat
                    (((with_reducible
                            rename Light.SameOn _ _ _ => apspMacro_188331_3));
                      ((try
                            have :=
                              apspMacro_188331_3 apspMacro_188331_0 (by omega)));
                      (revert apspMacro_188331_3)));
                (intros);
                (try simp only [Function.update_apply, Light.wrote] at *)));
            (omega))
        |
          ((((repeat
                    (((with_reducible
                            rename Light.SameOn _ _ _ => apspMacro_188331_4));
                      ((try
                            have :=
                              apspMacro_188331_4 apspMacro_188331_0 (by omega)));
                      (revert apspMacro_188331_4)));
                (intros);
                (try simp only [Function.update_apply, Light.wrote] at *)));
            (fail
                "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))))












variable {pS pE : ℕ}

/-- **One term**: step (2) and step (3) fill the part of the output below the term number `lam`. -/
theorem encodeTerm_spec (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeets lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hlam : lam < 10) (h : TermsDone μ out scr L a c lam μ') (r : ℤ) :
    Ends lim P d (encodeTerm pS pE) ⟨frame (locals L src out scr tab p7 p10 lam r), μ'⟩ (tTerm L)
      fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals L src out scr tab p7 p10 lam r'), μ''⟩ ∧
          TermsDone μ out scr L a c (lam + 1) μ'' := by
  have hplaces := pre.lay.places_succ
  -- The arguments of the two calls fit in a word, by the layout and the next three facts.
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  have hprod : ((lam * 10 ^ L : ℕ) : ℤ) = lam * 10 ^ L := by push_cast; rfl
  have hpow : ((7 ^ L : ℕ) : ℤ) = 7 ^ L := by push_cast; rfl
  unfold encodeTerm tTerm
  -- Res := encStep(src, scr, 7^L, lam, tab)
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
      |
        refine
          Light.Ends.callToThen
            ((encStep_meets hS (pre.toStep hlam h.2)) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (encStep_meets hS (pre.toStep hlam h.2)) ?_ ?_ ?_
            ?_);
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₁ μ₁
              ⟨hstep, same₁⟩
                  -- Res := encode(L, scr, out + lam 10^L, scr + 7^L, tab, p7, p10)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- Res := encode(L, scr, out + lam 10^L, scr + 7^L, tab, p7, p10)
  refine Ends.callTo (hrec _ _ _ _ _ _ (pre.toRec hlam h.2 hstep same₁)) ?_
  exact fun r₂ μ₂ hpost => ⟨r₂, μ₂, rfl, h.step pre.lay hlam same₁ hpost⟩

/-! ## The recursion -/

/-- **A leaf**: the number is copied. -/
theorem encode_leaf (pre : EncodePre lim μ src out scr tab p7 p10 V 0 a c) :
    Ends lim P d (encodeBody pS pE) ⟨frame [(0 : ℕ), src, out, scr, tab, p7, p10], μ⟩ (encTime 0)
      fun σ' => EncodePost μ out scr 0 a c σ'.mem := by
  ((obtain ⟨⟩ := id pre.lay); (obtain ⟨⟩ := id pre.lay.std))
  have hread : μ src = a 0 := pre.srcV 0 (by norm_num)
  -- if Level = 0 then mem[Out] := mem[Src]
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp) h) (hT := by simp [encTime])
  refine Ends.storeTo out (a 0) ⟨fun i hi => ?_, by ((try refine Light.SameOn.cell ?_);
                                                        (intro apspMacro_190388_0 apspMacro_190388_1);
                                                        (first
                                                          |
                                                            ((((repeat
                                                                      (((with_reducible
                                                                              rename Light.SameOn _ _ _ => apspMacro_190388_2));
                                                                        ((try
                                                                              have :=
                                                                                apspMacro_190388_2 apspMacro_190388_0 (by omega)));
                                                                        (revert apspMacro_190388_2)));
                                                                  (intros);
                                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                                              (omega))
                                                          |
                                                            ((simp [] at apspMacro_190388_1);
                                                              (((repeat
                                                                      (((with_reducible
                                                                              rename Light.SameOn _ _ _ => apspMacro_190388_3));
                                                                        ((try
                                                                              have :=
                                                                                apspMacro_190388_3 apspMacro_190388_0 (by omega)));
                                                                        (revert apspMacro_190388_3)));
                                                                  (intros);
                                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                                              (omega))
                                                          |
                                                            ((((repeat
                                                                      (((with_reducible
                                                                              rename Light.SameOn _ _ _ => apspMacro_190388_4));
                                                                        ((try
                                                                              have :=
                                                                                apspMacro_190388_4 apspMacro_190388_0 (by omega)));
                                                                        (revert apspMacro_190388_4)));
                                                                  (intros);
                                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                                              (fail
                                                                  "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                            its condition K x does not follow from the hypotheses."))))⟩
    (by (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega))) (by simp [encTime])
  obtain rfl : i = 0 := by simpa using hi
  exact Function.update_self ..

/-- **An inner vertex**: the two lengths are read from the tables, and the loop runs through the ten
terms. -/
theorem encode_node (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeets lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth) :
    Ends lim P d (encodeBody pS pE) ⟨frame [(L + 1 : ℕ), src, out, scr, tab, p7, p10], μ⟩
      (encTime (L + 1)) fun σ' => EncodePost μ out scr (L + 1) a c σ'.mem := by
  have hplaces := pre.lay.places_succ
  have haddr7 : ((p7 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p7 + L := by omega
  have haddr10 : ((p10 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p10 + L := by omega
  have hread7 := pre.p7V L (by omega)
  have hread10 := pre.p10V L (by omega)
  rw [encTime]
  -- if Level = 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) (fun _ => ?_)
  -- Len7 := mem[Pow7 + Level - 1]; Len10 := mem[Pow10 + Level - 1]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (7 ^ L : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr7,
                hread7]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr7, hread7] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr7, hread7] <;>
              omega)));
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
    (refine Light.Ends.setToThen (10 ^ L : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr10,
                hread10]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr10, hread10] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr10, hread10] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- for TermNo < 10: the parts of the output below the earlier terms are filled
  refine Ends.forShape (fun lam r μ' => ⟨frame (locals L src out scr tab p7 p10 lam r), μ'⟩)
    (TermsDone μ out scr L a c) 10 (tTerm L) 0 ⟨fun i hi => absurd hi (by omega), .refl⟩
    (fun lam r μ' hlam h => encodeTerm_spec hS hrec pre hd hlam h r)
    (fun _ μ' h => ⟨fun i hi => h.1 i (by rwa [pow_succ'] at hi), h.2⟩)
    (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT := by simp [tTerm]; omega)

/-- **encode** is correct and takes at most `encTime L` steps, in every program whose procedures
number pS and pE are encStep and encode.  It nests calls at most L deep. -/
theorem encode_spec (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodeBody pS pE))
    (hd : d + L ≤ lim.depth) (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) :
    Ends lim P d (encodeBody pS pE) ⟨frame [L, src, out, scr, tab, p7, p10], μ⟩ (encTime L)
      fun σ' => EncodePost μ out scr L a c σ'.mem := by
  induction L generalizing d μ src out scr V a with
  | zero => exact encode_leaf pre
  | succ L ih =>
    exact encode_node hS (fun _ _ _ _ _ _ pre' => Meets.of_body hE (ih (by omega) pre')) pre
      (by omega)

end Light.Sec2

end
end

section


/-!
# What encode computes, in the paper's terms

The result of encode is described by a recursion on positions in arrays (`encIdx`).  Here this is
linked with the definitions of the paper (Section 2.4.1) through arrays on strings as lists: if the
source holds an array on strings and the table holds the coefficients of the linear forms, then the
output holds the encoding of the array.

Both sides are treated at once, for an alphabet of seven variables with any coefficients:
`computeEncoding` is the procedure of Section 2.4.1 for such an alphabet,
`encIdx_eq_computeEncoding` says that the recursion on positions computes it, and `encode_str` is
the specification of encode in these terms. For the two alphabets of the paper the procedure gives
the two encodings (`computeEncoding_phi`, `computeEncoding_psi`).
-/

public section

open ThreeSumApsp

namespace Light.Sec2

open Finset ThreeSumApsp.Spec

/-! ## From positions to strings -/

section
variable {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)

/-- The recursion on positions computes the procedure of Section 2.4.1, if the array and the table
of coefficients are stored by digits. -/
private theorem encIdx_eq_computeEncoding {c : ℕ → ℤ}
    (hc : ∀ lam s, c (7 * (termIdx lam : ℕ) + (e s : ℕ)) = coef lam s) (L : ℕ)
    (A : (Fin L → α) → ℤ) {arr : ℕ → ℤ}
    (harr : ∀ j < 7 ^ L, arr j = A (decodeStr e L j)) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c L arr i = computeEncoding coef L A (decodeT L i) := by
  induction L generalizing arr i with
  | zero =>
    rw [encIdx, computeEncoding, harr 0 (by norm_num)]
    exact congrArg A (Subsingleton.elim _ _)
  | succ L ih =>
    -- The first digit of i is the digit of a term λ, and the rest of i is the code of a leaf below.
    have hpos : 0 < 10 ^ L := by positivity
    have hdigit : i / 10 ^ L < 10 := by rwa [Nat.div_lt_iff_lt_mul hpos, ← pow_succ']
    have hrest : i % 10 ^ L < 10 ^ L := Nat.mod_lt _ hpos
    obtain ⟨lam, hidx⟩ : ∃ lam : Term, ((termEquiv lam : Fin 10) : ℕ) = i / 10 ^ L :=
      ⟨termOfNat _, termIdx_termOfNat hdigit⟩
    have hleaf : decodeT (L + 1) i = Fin.cons lam (decodeT L (i % 10 ^ L)) := by
      have hcons := decodeStr_cons termEquiv lam hrest
      rwa [hidx, Nat.div_add_mod'] at hcons
    rw [encIdx, hleaf, computeEncoding, Fin.cons_zero, Fin.tail_cons]
    unfold encSlice
    -- Step (2) of the procedure of Section 2.4.1: the sum over the digits is the sum over the
    -- variables.
    refine ih _ (fun j hj => ?_) hrest
    rw [← Fin.sum_univ_eq_sum_range (fun s => c (7 * (i / 10 ^ L) + s) * arr (s * 7 ^ L + j)) 7,
      ← e.sum_comp fun s : Fin 7 => c (7 * (i / 10 ^ L) + (s : ℕ)) * arr ((s : ℕ) * 7 ^ L + j)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sliceAt, ← hidx, show ((termEquiv lam : Fin 10) : ℕ) = termIdx lam from rfl, hc,
      harr _ (by rw [pow_succ']; exact Nat.mul_add_lt_mul (e s).isLt hj), decodeStr_cons e s hj]

end

/-! ## The specification of encode, on lists -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out scr tab p7 p10 L : ℕ} {V : ℤ}

/-- The hypotheses of encode hold if the source, the table of coefficients and the two tables of
powers are in their places and the numbers obey the bounds. -/
private theorem EncodePre.of_seg {l T : List ℤ} (lay : EncodeLayout lim src out scr tab p7 p10 L)
    (hl : l.length = 7 ^ L) (hsrc : Seg μ src l) (hV : ∀ x ∈ l, -V ≤ x ∧ x ≤ V)
    (hT : T.length = 70) (htab : Seg μ tab T) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) :
    EncodePre lim μ src out scr tab p7 p10 V L (fun j => l.getD j 0) (fun i => T.getD i 0) :=
  { lay := lay
    srcV := fun j hj => hsrc.getD (by omega) 0
    src_bound := fun j hj => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hV _ (List.getElem_mem _)
    tabV := fun i hi => htab.getD (by omega) 0
    coef_bound := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hc _ (List.getElem_mem _)
    p7V := h7, p10V := h10, word_bound := hVB }

/-- **The encoding of an array on strings** (Section 2.4.1), for both alphabets at once.  If the
source holds the array A on the strings of length L, the table holds the coefficients, the tables of
powers are in their places and the numbers obey the bounds, then encode ends within `cEncode · 10^L`
steps, the output holds what the procedure of Section 2.4.1 computes, and only the output and the
scratch area have changed. -/
theorem encode_str {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ) {T : List ℤ}
    (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) {pS pE : ℕ}
    (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodeBody pS pE))
    (lay : EncodeLayout lim src out scr tab p7 p10 L) (A : (Fin L → α) → ℤ)
    (hsrc : Seg μ src (arrStr e A)) (hV : ∀ u, |A u| ≤ V) (htab : Seg μ tab T)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) (hd : d + L ≤ lim.depth) :
    Ends lim P d (encodeBody pS pE) ⟨frame [L, src, out, scr, tab, p7, p10], μ⟩ (cEncode * 10 ^ L)
      fun σ' => Seg σ'.mem out (arrT (computeEncoding coef L A)) ∧
        SameOutside2 μ σ'.mem out (10 ^ L) scr (scrSize L) := by
  have hbound : ∀ x ∈ arrStr e A, -V ≤ x ∧ x ≤ V := fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact abs_le.1 (hV _)
  have pre := EncodePre.of_seg lay (length_arrStr e A) hsrc hbound hT htab hc h7 h10 hVB
  refine (encode_spec hS hE hd pre).mono (by have := encTime_le L; omega) fun σ' h => ⟨?_, h.2⟩
  intro i hi
  rw [length_arrT] at hi
  rw [h.1 i hi,
    encIdx_eq_computeEncoding e coef hcoef L A (fun j hj => getD_arrStr_of_lt e A hj) hi,
    ← List.getD_eq_getElem _ 0, arrT, getD_arrStr_of_lt termEquiv _ hi]
  rfl

end Light.Sec2

end
end

section


/-!
# What the callers of encode assume

The callers of encode (Section 2.4.1) assume a specification of the procedure that does not name its
body: `EncodeLSpec` for the array a and the forms φ_λ, `EncodeRSpec` for b and ψ_λ.  Both hold for
every program that has encStep and encode at their numbers.  The places that the callers provide are
a layout for encode (`EncodePlaces.layout`), so the specification of encode on lists applies
(`encode_entry`, for any alphabet of seven variables); the two specifications are its cases for the
left variables with the forms φ_λ and for the right variables with the forms ψ_λ.
-/

public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {n Lmax src dst scr tab p7 p10 : ℕ} {μ : ℕ → ℤ}

/-- The scratch area of encode has fewer than 7^L cells. -/
private theorem scrSize_le (L : ℕ) : scrSize L + 1 ≤ 7 ^ L := by
  induction L with
  | zero => simp [scrSize]
  | succ L ih =>
    rw [scrSize, pow_succ]
    omega

/-- The places that the callers provide are a layout for encode. -/
theorem EncodePlaces.layout (std : Std lim)
    (h : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ) :
    EncodeLayout lim src dst scr tab p7 p10 n := by
  (obtain ⟨⟩ := id h)
  have hscr := scrSize_le n
  exact ⟨std, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A cell of a table of powers. -/
private theorem pow_of_seg {p b : ℕ} (h : Seg μ p (powList b (Lmax + 1))) (hn : n ≤ Lmax) :
    ∀ i < n, μ (p + i) = ((b ^ i : ℕ) : ℤ) := fun i hi => by
  rw [h.get (i := i) (by simp; omega), getElem_powList]

/-- **The specification that the callers of encode assume**, for any alphabet of seven variables.
The callers allow `7^n` cells of scratch area, more than the `scrSize n` that `encode` uses. -/
theorem encode_entry {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)
    {T : List ℤ} (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) (std : Std lim)
    (hS : P[pEncStep]? = some encStepBody) (hE : P[pEncode]? = some (encodeBody pEncStep pEncode))
    {d : ℕ} (hd : d + (n + 1) ≤ lim.depth) (hpl : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ)
    (htab : Seg μ tab T) (A : (Fin n → α) → ℤ) (hsrc : Seg μ src (arrStr e A)) {V : ℤ}
    (hV : ∀ u, |A u| ≤ V) (hVB : 7 ^ (n + 1) * V ≤ lim.word) :
    Meets lim P pEncode d [n, src, dst, scr, tab, p7, p10] μ (cEncode * 10 ^ n) fun _ μ' =>
      Seg μ' dst (arrT (computeEncoding coef n A)) ∧
        SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n) := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV fun _ => e.symm 0)
  have hVB' : ((7 ^ n : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ hVB
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hV0
  have hscr := scrSize_le n
  refine .of_body hE ((encode_str e coef hT hc hcoef hS hE (hpl.layout std) A hsrc hV htab
    (pow_of_seg hpl.hp7 hpl.n_le) (pow_of_seg hpl.hp10 hpl.n_le) hVB' (by omega)).mono le_rfl
    fun σ' h => ⟨h.1, h.2.mono fun x hx => by omega⟩)

/-- **The specification that the callers of encode assume, for the array a.** -/
theorem encodeL_entry (std : Std lim) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncode]? = some (encodeBody pEncStep pEncode)) : EncodeLSpec lim P cEncode := by
  intro n Lmax src dst scr tab p7 p10 μ a V hpl htab hsrc hV hVB d hd
  exact computeEncoding_phi a ▸ encode_entry leftEquiv phi (by decide) (by decide) phiFlat_spec std
    hS hE hd hpl htab a hsrc hV hVB

/-- **The specification that the callers of encode assume, for the array b.** -/
theorem encodeR_entry (std : Std lim) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncode]? = some (encodeBody pEncStep pEncode)) : EncodeRSpec lim P cEncode := by
  intro n Lmax src dst scr tab p7 p10 μ b V hpl htab hsrc hV hVB d hd
  exact computeEncoding_psi b ▸ encode_entry rightEquiv psi (by decide) (by decide) psiFlat_spec std
    hS hE hd hpl htab b hsrc hV hVB

end Light.Sec2

end
end

section


/-!
# Three routines of the library, as their callers see them

The programs for Theorem 5 call their procedures by number, and a caller assumes a specification of
the procedure that does not name its body: PowSpec for the tables of powers, FillSpec for filling a
segment, SqrtSpec for the square root.  Each follows from the specification of the routine in the
library; pow first puts its arguments in the order of the library's routine.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {c : ℕ}

/-! ## The tables of powers -/










/-- **pow(b, n, dst)** writes the powers b^0, …, b^n to the cells from dst, within 35 (n + 1) steps.
-/
theorem pow_entry (std : Std lim) (hP : P[pPow]? = some powBody) (hc : 35 ≤ c) :
    PowSpec lim P c := by
  intro b n dst μ hdst1 hdst hb hpow d _
  have hw := std.space_le
  have h100 := std.const_le
  refine .mono_const (.of_body hP ?_) hc
  -- The arguments b, n, dst become dst, n + 1, b.
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen b ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen dst ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen b ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (n + 1 : ℕ) ?_ ?_ ?_);
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
  refine (powTable_ends (dst := dst) (L := n + 1) (b := b) 0 0 [b] hw hdst fun j hj => ?_).mono
    (by simp [powTableTime]; omega) fun _ h => h
  exact le_trans (by exact_mod_cast Nat.pow_le_pow_right hb hj) hpow

/-! ## Filling a segment -/







/-! ## The square root -/

/-- **sqrt(K)** returns ⌊√K⌋, within 18 (⌊√K⌋ + 1) steps. -/
theorem sqrt_entry (hP : P[pSqrt]? = some sqrtBody) (hc : 18 ≤ c) : SqrtSpec lim P c :=
  fun _ μ hw _ _ =>
    ((sqrt_meets hP μ (by push_cast at hw ⊢; omega)).mono_time (by simp; omega)).mono_const hc

end Light.Sec2

end
end

section


/-!
# Band and block of every row, by counting (Section 2.3.4)

Section 2.3.4 cuts the N rows of X into bands of K₀ blocks of N₀ rows.  counters(N, K0, N0, dst)
writes, for every row I < N, its band I / (K0 N0) to the cell dst + I and its block I / N0 % K0 to
the cell dst + N + I.  There is no division: three counters (band, block, offset) are stepped from
each row to the next, as `Spec.stepCtr` says, and `Spec.ctrAt_succ` says that they are the
quotients and remainders.

A round writes two cells (`Counted.step`) and steps the counters (`countersRound_spec`);
`counters_spec` runs through the rows, and `counters_entry` is the specification that the callers of
the procedure assume.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Counters












end Counters





















namespace Counters

variable {μ μ' : ℕ → ℤ} {N K0 N0 dst i : ℕ}







/-- The two cells that round i writes. -/
theorem Counted.step (h : Counted μ N K0 N0 dst i μ') (hi : i < N) :
    Counted μ N K0 N0 dst (i + 1) (Function.update (Function.update μ' (dst + i)
      ((Spec.ctrAt K0 N0 i).band : ℕ)) (dst + N + i) ((Spec.ctrAt K0 N0 i).block : ℕ)) := by
  refine ⟨fun I hI => ?_, (h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hI with hI | rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h.1 I hI
  · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
    exact ⟨rfl, rfl⟩






end Counters

open Counters

variable {μ : ℕ → ℤ} {N K0 N0 dst : ℕ}

/-- **One round** writes the band and the block of row `i` and steps the counters to those of row
`i + 1`. -/
theorem countersRound_spec (std : Std lim) (hsp : dst + 2 * N ≤ lim.space) (hK : 0 < K0)
    (hN0 : 0 < N0) (hw : ((K0 + N0 : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < N) {σ : State}
    (h : Inv μ N K0 N0 dst i σ) :
    Ends lim P d countersRound σ countersRound.blockCost (Inv μ N K0 N0 dst (i + 1)) := by
  obtain ⟨μ', rfl, hI⟩ := h
  (obtain ⟨⟩ := id std)
  push_cast at hw
  have hnext := Spec.ctrAt_succ hK hN0 i
  have hstep := hI.step hi
  have hband : (Spec.ctrAt K0 N0 i).band ≤ i := Nat.div_le_self _ _
  have hblock : (Spec.ctrAt K0 N0 i).block < K0 := Nat.mod_lt _ hK
  have hoff : (Spec.ctrAt K0 N0 i).off < N0 := Nat.mod_lt _ hN0
  generalize Spec.ctrAt K0 N0 i = c at *
  unfold countersRound
  rw [Spec.stepCtr] at hnext
  -- mem[dst + Row] := Band; mem[dst + N + Row] := Block; Row := Row + 1; Offset := Offset + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (dst + i) c.band ?_ ?_ ?_);
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
    (refine Light.Ends.storeToThen (dst + N + i) c.block ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_);
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
          (c.off + 1 : ℕ)
            -- if Offset < N0
            
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
  -- if Offset < N0
  refine Ends.iteLast (fun hc => Ends.skip ⟨_, ?_, hstep⟩) fun hc => ?_
  · -- The next row of the same block.
    rw [hnext, if_pos (by simp at hc; omega)]
    rfl
  -- Offset := 0; Block := Block + 1; if Block < K0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (c.block + 1 : ℕ) ?_ ?_ ?_);
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
  refine Ends.iteLast (fun hc' => Ends.skip ⟨_, ?_, hstep⟩) fun hc' => ?_
  · -- The first row of the next block of the same band.
    rw [hnext, if_neg (by simp at hc; omega), if_pos (by simp at hc'; omega)]
    rfl
  · -- The first row of the first block of the next band: Block := 0; Band := Band + 1
    refine Ends.setToThen 0 (Ends.setTo ((c.band + 1 : ℕ) : ℤ) ⟨_, ?_, hstep⟩)
    rw [hnext, if_neg (by simp at hc; omega), if_neg (by simp at hc'; omega)]
    rfl

/-- **counters** writes the band and the block of every row and changes nothing else. -/
theorem counters_spec (std : Std lim) (hsp : dst + 2 * N ≤ lim.space) (hK : 0 < K0) (hN0 : 0 < N0)
    (hw : ((K0 + N0 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d countersBody ⟨frame [N, K0, N0, dst], μ⟩ (44 * (N + 1)) fun σ' =>
      (∀ I < N, σ'.mem (dst + I) = (I / (K0 * N0) : ℕ) ∧
        σ'.mem (dst + N + I) = (I / N0 % K0 : ℕ)) ∧ SameOutside μ σ'.mem dst (2 * N) := by
  have hspace := std.space_le
  -- while Row < N; a round takes at most 40 steps
  refine Ends.whileConst (Inv μ N K0 N0 dst) N countersRound.blockCost ?start ?round ?done
    (by simp [countersRound]; omega)
  case start =>
    refine ⟨μ, ?_, fun I hI => absurd hI (by omega), .refl⟩
    -- The row and the three counters start at 0.
    rw [← frame_append_zeros _ 4]
    simp [Spec.ctrAt]
  case round =>
    intro i σ hi h
    have hround := countersRound_spec (P := P) (d := d) std hsp hK hN0 hw hi h
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hround⟩
  case done =>
    rintro _ ⟨μ', rfl, hcells, same⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hcells, same⟩

/-- **The specification that the callers of counters assume.** -/
theorem counters_entry (std : Std lim) (hP : P[pCounters]? = some countersBody) {c : ℕ}
    (hc : 44 ≤ c) : CountersSpec lim P c :=
  fun _ _ _ _ _ hsp hK hN0 hw _ _ => .mono_const (.of_body hP (counters_spec std hsp hK hN0 hw)) hc

end Light.Sec2

end
end

section


/-!
# A binomial coefficient, by Pascal's triangle

Section 2.3.4 needs the number K = (L choose m) of subsets of size m.  binom(L, m, pas) returns this
binomial coefficient.  The cells pas, …, pas + L hold a row of Pascal's triangle.  Row 0 is 1
followed by zeros (`binomFirst_spec`), and the next row is formed in place, from right to left, so
that the two entries that are added are still those of the old row.  `binomPlace_spec` treats one
entry, by Pascal's rule, `binomInner_spec` one row, and `binom_spec` runs through the rows;
`binom_entry` is the specification that the callers of the procedure assume.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Binom









end Binom

open Binom



























namespace Binom

/-! ## One row from the row before it -/








/-- One more entry has been replaced. -/
theorem Mixed.step {μ μ' : ℕ → ℤ} {L pas i p : ℕ} (h : Mixed μ L pas i (p + 1) μ')
    (hp : p + 1 ≤ L) :
    Mixed μ L pas i p (Function.update μ' (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ)) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  by_cases hjp : j = p + 1
  · rw [hjp, Function.update_self, if_pos (by omega)]
  · rw [Function.update_of_ne (by omega), h.1 j hj]
    exact if_congr (by omega) rfl rfl

variable {μ : ℕ → ℤ} {L m pas i : ℕ} {T : ℕ} {Q : State → Prop}





/-- **One entry**, by Pascal's rule. -/
theorem binomPlace_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) {r : ℕ} (hr : r < L) {σ : State}
    (h : Inv μ L m pas i r σ) :
    Ends lim P d binomPlace σ binomPlace.blockCost (Inv μ L m pas i (r + 1)) := by
  obtain ⟨μ', rfl, hI⟩ := h
  (obtain ⟨⟩ := id std)
  obtain ⟨p, hp⟩ : ∃ p, L - r = p + 1 := ⟨L - r - 1, by omega⟩
  unfold Inv
  rw [hp] at hI ⊢
  rw [show L - (r + 1) = p by omega]
  -- The two entries that are added are still those of row i, and their sum fits in a word.
  have habove : μ' (pas + (p + 1)) = (i.choose (p + 1) : ℕ) := by
    rw [hI.1 (p + 1) (by omega), if_neg (by omega)]
  have hleft : μ' (pas + p) = (i.choose p : ℕ) := by rw [hI.1 p (by omega), if_neg (by omega)]
  have hsum : (i + 1).choose (p + 1) = i.choose p + i.choose (p + 1) := Nat.choose_succ_succ' i p
  have hfits : (i + 1).choose (p + 1) ≤ 2 ^ L :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hi)
  have haddr : ((pas : ℤ) + ((p : ℤ) + 1) - 1).toNat = pas + p := by omega
  have haddr' : ((pas : ℤ) + ((p : ℤ) + 1)).toNat = pas + (p + 1) := by omega
  unfold binomPlace
  -- mem[pas + Place] := mem[pas + Place] + mem[pas + Place - 1]; Place := Place - 1
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
        Light.Ends.storeToThen (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ) ?_ ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, habove,
                hleft, haddr, haddr', hsum]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [habove, hleft, haddr, haddr', hsum] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, habove, hleft, haddr,
                haddr', hsum] <;>
              omega)));
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
    (refine Light.Ends.setToThen p ?_ ?_ ?_);
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
  exact ⟨_, rfl, hI.step (by omega)⟩

/-- **One row**: the loop over the places turns row i of the triangle into row i + 1. -/
theorem binomInner_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) (hrow : ∀ j ≤ L, μ (pas + j) = (i.choose j : ℕ))
    (done : ∀ μ' : ℕ → ℤ, (∀ j ≤ L, μ' (pas + j) = ((i + 1).choose j : ℕ)) →
      SameOutside μ μ' pas (L + 2) → Q ⟨frame [L, m, pas, i, 0], μ'⟩)
    (hT : 23 * L + 4 ≤ T) :
    Ends lim P d binomInner ⟨frame [L, m, pas, i, L], μ⟩ T Q := by
  have h100 := std.const_le
  -- while 0 < Place
  refine Ends.whileConst (Inv μ L m pas i) L binomPlace.blockCost ?start ?round ?done
    (by simp [binomPlace]; omega)
  case start => exact ⟨μ, rfl, fun j hj => by rw [if_neg (by omega), hrow j hj], .refl⟩
  case round =>
    intro r σ hr h
    have hplace := binomPlace_spec (P := P) (d := d) std hsp hi hw hr h
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hplace⟩
  case done =>
    rintro _ ⟨μ', rfl, hcells, same⟩
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    have hdone := done μ' (fun j hj => ?_) same
    · simpa using hdone
    · -- Entry 0 is 1 in every row.
      rw [hcells j hj, Nat.sub_self]
      split_ifs with hj0
      · rfl
      · rw [show j = 0 by omega, Nat.choose_zero_right, Nat.choose_zero_right]

/-! ## The loop over the rows -/









/-- **One round of the loop over the rows** turns row `i` of the triangle into row `i + 1`. -/
theorem binomRow_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) {σ : State} (h : RowAt μ L m pas i σ) :
    Ends lim P d binomRow σ (tRow L) (RowAt μ L m pas (i + 1)) := by
  obtain ⟨p, μ', rfl, hrow, same⟩ := h
  (obtain ⟨⟩ := id std)
  unfold binomRow tRow
  -- Place := L
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen L ?_ ?_ ?_);
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
  refine Ends.next _ (binomInner_spec std hsp hi hw hrow ?_ le_rfl)
  intro μ'' hnew same'
  -- Row := Row + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_);
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
  exact ⟨_, _, rfl, hnew, same.trans same'⟩

/-- **Row 0** of the triangle is written: 1 followed by `L` zeros. -/
theorem binomFirst_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space)
    (done : ∀ σ, RowAt μ L m pas 0 σ → Q σ) (hT : 15 * L + 11 ≤ T) :
    Ends lim P d binomFirst ⟨frame [L, m, pas], μ⟩ T Q := by
  (obtain ⟨⟩ := id std)
  -- mem[pas] := 1; Place := 1; while Place < L + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen pas 1 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 + 1 : ℕ) ?_ ?_ ?_);
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
  refine Ends.whileBlock
    (fun q σ => σ = ⟨frame [L, m, pas, 0, (q + 1 : ℕ)],
      wrote (Function.update μ pas 1) (pas + 1) (fun _ => 0) q⟩) L ?start ?round ?done
  case start =>
    rw [wrote_zero]
    rfl
  case round =>
    rintro q _ hq rfl
    have haddr : ((pas : ℤ) + ((q : ℤ) + 1)).toNat = pas + 1 + q := by omega
    -- mem[pas + Place] := 0; Place := Place + 1
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      by simp [update_frame_setLocal, ← wrote_succ, haddr]⟩
  case done =>
    rintro _ rfl
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), done _ ⟨_, _, rfl, fun j hj => ?_,
      (SameOutside.refl.update ⟨by omega, by omega⟩ 1).trans
        ((sameOutside_wrote le_rfl).mono (by omega) (by omega))⟩⟩
    -- (0 choose 0) = 1, and (0 choose j + 1) = 0.
    cases j with
    | zero => rw [wrote_rest (Or.inl (by omega)), Nat.add_zero, Function.update_self]; rfl
    | succ j => rw [← Nat.add_assoc, Nat.add_right_comm, wrote_done (by omega)]; rfl

end Binom

variable {μ : ℕ → ℤ} {L m pas : ℕ}

/-- **binom** returns (L choose m) and changes no cell outside the L + 2 cells from pas. -/
theorem binom_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hm : m ≤ L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d binomBody ⟨frame [L, m, pas], μ⟩ (30 * (L + 1) ^ 2) fun σ' =>
      σ'.loc 0 = (L.choose m : ℕ) ∧ SameOutside μ σ'.mem pas (L + 2) := by
  (obtain ⟨⟩ := id std)
  -- Row 0.
  refine Ends.next _ (binomFirst_spec std hsp ?_ le_rfl) (by ring_nf; omega)
  intro σ hfirst
  -- while Row < L; the L rounds take L (23 L + 14) steps
  refine Ends.next _ (Ends.whileConst (RowAt μ L m pas) L (tRow L) hfirst ?round ?done le_rfl)
    (by simp [tRow]; ring_nf; omega)
  case round =>
    intro i σ hi h
    have hrow := binomRow_spec (P := P) (d := d) std hsp hi hw h
    obtain ⟨p, μ', rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrow⟩
  case done =>
    rintro _ ⟨p, μ', rfl, hrow, same⟩
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- The result: local 0 := mem[pas + m]
    exact Ends.setTo (L.choose m : ℕ) ⟨by simp, same⟩
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hrow m hm] <;> omega))) (by simp [tRow]; ring_nf; omega)

/-- **The specification that the callers of binom assume.** -/
theorem binom_entry (std : Std lim) (hP : P[pBinom]? = some binomBody) {c : ℕ} (hc : 30 ≤ c) :
    BinomSpec lim P c :=
  fun _ _ _ _ hsp hm hw _ _ => .mono_const (.of_body hP (binom_spec std hsp hm hw)) hc

end Light.Sec2

end
end

section


/-!
# The tables of the coefficients of Schönhage's identity

Section 2.2 defines, for each of the ten terms λ of Schönhage's identity, two linear forms φ_λ and
ψ_λ in seven variables each; step (2) of the recursion applies them.  coef(phi) writes the
coefficient φ_λ(s) of the variable number s < 7 in the form of the term number λ < 10 to the cell
phi + 7 λ + s, and ψ_λ(t) to the cell phi + 70 + 7 λ + t.  The body is a straight line of 140
stores, made from the two tables `Spec.phiTable` and `Spec.psiTable`.  `storeSigns_spec` treats
such a line of stores by induction on the list, and `coef_entry`, the specification that the callers
of the procedure assume, applies it to the two tables.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}
















/-- A coefficient's expression stays within the limits and gives the coefficient. -/
private theorem signExpr_gives (h1 : (1 : ℤ) ≤ lim.word) {x : ℤ} (hx : x = 1 ∨ x = 0 ∨ x = -1)
    (σ : State) : (signExpr x).Gives lim σ x := by
  rcases hx with rfl | rfl | rfl <;> simp [signExpr] <;> omega

/-- A coefficient's expression costs at most 3 steps. -/
private theorem signExpr_cost (x : ℤ) : (signExpr x).cost ≤ 3 := by
  unfold signExpr
  split_ifs <;> simp

/-- **storeSigns** writes the list to the cells from base + i on, changes nothing else, and takes
at most 7 steps for each number. -/
theorem storeSigns_spec (std : Std lim) {base : ℕ} (l : List ℤ) (i : ℕ) (μ : ℕ → ℤ)
    (hl : ∀ x ∈ l, x = 1 ∨ x = 0 ∨ x = -1) (hsp : base + i + l.length ≤ lim.space) :
    Ends lim P d (storeSigns i l) ⟨frame [base], μ⟩ (7 * l.length) fun σ' =>
      Seg σ'.mem (base + i) l ∧ SameOutside μ σ'.mem (base + i) l.length := by
  (obtain ⟨⟩ := id std)
  induction l generalizing i μ with
  | nil => exact Ends.skip ⟨Seg.nil, .refl⟩
  | cons x l ih =>
    rw [List.length_cons] at hsp ⊢
    have hcost := signExpr_cost x
    -- mem[phi + i] := x, in at most 7 steps, and then the rest of the list
    refine Ends.storeToThen (base + i) x
      ((ih (i + 1) _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by omega)).mono
        (by simp; omega) ?_)
      (he := ⟨by (((try have := Light.Std.space_le (by assumption)));
                     ((try have := Light.Std.const_le (by assumption)));
                     (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), signExpr_gives (by omega) (hl x List.mem_cons_self) _, by omega⟩)
      (hT := by simp; omega)
    rintro σ' ⟨hrest, same⟩
    refine ⟨seg_cons.2 ⟨?_, by rwa [Nat.add_assoc]⟩, fun b hb => ?_⟩
    · rw [same (base + i) (Or.inl (by omega)), Function.update_self]
    · rw [same b (by omega), Function.update_of_ne (by omega)]

/-- All coefficients are 1, 0 or -1. -/
private theorem coef_signs :
    ∀ x ∈ Spec.phiFlat ++ Spec.psiFlat, x = 1 ∨ x = 0 ∨ x = -1 := by
  simp [Spec.phiFlat, Spec.psiFlat, Spec.phiTable, Spec.psiTable]

/-- **coef** writes the two tables and changes nothing else, in 7 · 140 steps: the specification
that its callers assume. -/
theorem coef_entry (std : Std lim) (hP : P[pCoef]? = some coefBody) {c : ℕ} (hc : 980 ≤ c) :
    CoefSpec lim P c := by
  intro phi μ hsp d _
  have hlen : (Spec.phiFlat ++ Spec.psiFlat).length = 140 := by simp
  have hphi := Spec.length_phiFlat
  refine ⟨coefBody, hP, (storeSigns_spec std _ 0 μ coef_signs (by omega)).mono (by omega) ?_⟩
  rintro σ' ⟨hcells, same⟩
  rw [Nat.add_zero] at hcells same
  obtain ⟨hphiCells, hpsiCells⟩ := seg_append.1 hcells
  exact ⟨hphiCells, hphi ▸ hpsiCells, hlen ▸ same⟩

end Light.Sec2

end
end

section


/-!
# Tables of digits, by an odometer

The programs for Theorem 5 turn the number of a row or of a column into a string ("locate the output
strings", in the proof of Theorem 5), so they need the digits of these numbers in base 3 and in
base 4. digits(n, b, len, dst) writes, for every x < n, the len digits of x % b^len in base b, most
significant first, to the len cells from dst + x * len.  There is no division: row 0 is zero, and
row x + 1 is row x plus one, formed from the least significant digit on with a carry.

* The pure side: `carryInto b j x` is the carry into the place of weight b^j when 1 is added to x,
  defined as the routine computes it, and `placeDigit_succ` says that a place of x plus its carry,
  reduced if it reaches b, is the place of x + 1.
* `digitsPlace_spec` treats one place, `digitsInner_spec` one row, `digitsZero_spec` row 0, and
  `digits_spec` runs through the rows; `digits_entry` is the specification that the callers of the
  procedure assume.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

namespace Digits

/-! ## Adding 1 to a number, place by place -/










/-- A digit is less than the base. -/
private theorem placeDigit_lt {b : ℕ} (hb : 0 < b) (j x : ℕ) : placeDigit b j x < b :=
  Nat.mod_lt _ hb

/-- A carry is 0 or 1. -/
private theorem carryInto_le_one (b j x : ℕ) : carryInto b j x ≤ 1 := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [carryInto]
    split_ifs <;> omega

/-- Adding a carry c to q: the last digit of q grows by c, or becomes 0 and gives a carry. -/
private theorem add_carry {b : ℕ} (hb : 0 < b) (q : ℕ) {c : ℕ} (hc : c ≤ 1) :
    (q + c) / b = q / b + (if q % b + c < b then 0 else 1) ∧
      (q + c) % b = if q % b + c < b then q % b + c else 0 := by
  have hlt : q % b < b := Nat.mod_lt q hb
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  · simp [hlt]
  · split_ifs with h
    · exact Nat.succ_div_mod_of_lt h
    · exact Nat.succ_div_mod_of_eq (by omega)

/-- The digits of x + 1 from the place of weight b^j on are those of x plus the carry. -/
private theorem succ_div_pow {b : ℕ} (hb : 0 < b) (j x : ℕ) :
    (x + 1) / b ^ j = x / b ^ j + carryInto b j x := by
  induction j with
  | zero => simp [carryInto]
  | succ j ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih, (add_carry hb _ (carryInto_le_one b j x)).1,
      Nat.div_div_eq_div_mul]
    rfl

/-- **One place of the odometer.**  The digit of x + 1 is the digit of x plus the carry, or 0 if
this reaches b. -/
theorem placeDigit_succ {b : ℕ} (hb : 0 < b) (j x : ℕ) :
    placeDigit b j (x + 1) =
      if placeDigit b j x + carryInto b j x < b then placeDigit b j x + carryInto b j x else 0 := by
  rw [placeDigit, succ_div_pow hb, (add_carry hb _ (carryInto_le_one b j x)).2]
  rfl

/-- The digits below place len do not change when the number is reduced modulo b^len. -/
private theorem mod_pow_div_mod (b c : ℕ) {j len : ℕ} (hj : j < len) :
    c % b ^ len / b ^ j % b = c / b ^ j % b := by
  obtain ⟨e, rfl⟩ : ∃ e, len = j + (e + 1) := ⟨len - j - 1, by omega⟩
  rw [Nat.pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self b e.succ_ne_zero)]

/-- The entry number q of the row of x. -/
private theorem getElem_digitList {b len x q : ℕ} (hq : q < len)
    (h : q < (ThreeSumApsp.digitList b len (x % b ^ len)).length) :
    (ThreeSumApsp.digitList b len (x % b ^ len))[q] = placeDigit b (len - 1 - q) x := by
  simp [ThreeSumApsp.digitList, ThreeSumApsp.digit, placeDigit,
    mod_pow_div_mod b x (show len - 1 - q < len by omega)]

/-! ## The program -/















end Digits

open Digits

variable {lim : Limits} {P : Program} {d : ℕ}







































namespace Digits

/-! ## One row from the row before it -/






/-- One more place. -/
theorem Placed.step {μ μ' : ℕ → ℤ} {b len cur y r : ℕ} (h : Placed μ b len cur y r μ')
    (hr : r < len) :
    Placed μ b len cur y (r + 1)
      (Function.update μ' (cur + (len - 1 - r)) (placeDigit b r (y + 1) : ℕ)) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [Function.update_of_ne (by omega)]
    exact h.1 j hj
  · exact Function.update_self ..







variable {μ : ℕ → ℤ} {n b len dst row cur prev y : ℕ} {T : ℕ} {Q : State → Prop}

/-- **One place** of the new row is written, and the carry into the next place is formed. -/
theorem digitsPlace_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hcur : cur + len ≤ lim.space) (hprev : prev + len ≤ cur)
    (hrow : ∀ q < len, μ (prev + q) = (placeDigit b (len - 1 - q) y : ℕ)) {r : ℕ} (hr : r < len)
    {σ : State} (h : Inv μ n b len dst row cur prev y r σ) :
    Ends lim P d digitsPlace σ digitsPlace.blockCost
      (Inv μ n b len dst row cur prev y (r + 1)) := by
  obtain ⟨x, μ', rfl, hI⟩ := h
  (obtain ⟨⟩ := id std)
  have hdigit := placeDigit_lt (show 0 < b by omega) r y
  have hcarry := carryInto_le_one b r y
  have hnew := placeDigit_succ (show 0 < b by omega) r y
  have hstep := hI.step hr
  rw [show len - 1 - r = len - (r + 1) by omega, hnew] at hstep
  -- The digit of the row before has not been overwritten.
  have hread : μ' (prev + (len - (r + 1))) = (placeDigit b r y : ℕ) := by
    rw [hI.2 _ (Or.inl (by omega)), hrow _ (by omega), show len - 1 - (len - (r + 1)) = r by omega]
  unfold digitsPlace
  -- Place := Place - 1; Digit := mem[Prev + Place] + Carry
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (len - (r + 1) : ℕ) ?_ ?_ ?_);
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
        Light.Ends.setToThen (placeDigit b r y + carryInto b r y : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hread] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if Digit < b
  refine Ends.iteLast (fun hc => ?_) fun hc => ?_
  · -- No carry out of this place: mem[Cur + Place] := Digit; Carry := 0
    have hlt : placeDigit b r y + carryInto b r y < b := by simp at hc; omega
    rw [if_pos hlt] at hstep
    refine Ends.storeToThen (cur + (len - (r + 1))) ((placeDigit b r y + carryInto b r y : ℕ) : ℤ)
      (Ends.setTo ((0 : ℕ) : ℤ) ⟨((placeDigit b r y + carryInto b r y : ℕ) : ℤ), _, ?_, hstep⟩)
    rw [carryInto, if_pos hlt]
    rfl
  · -- A carry out of this place, so the carry into it was 1 and stays: mem[Cur + Place] := 0
    have hlt : ¬ placeDigit b r y + carryInto b r y < b := by simp at hc; omega
    rw [if_neg hlt] at hstep
    refine Ends.storeTo (cur + (len - (r + 1))) ((0 : ℕ) : ℤ)
      ⟨((placeDigit b r y + carryInto b r y : ℕ) : ℤ), _, ?_, hstep⟩
    rw [carryInto, if_neg hlt, show carryInto b r y = 1 by omega]
    rfl

/-- **One row**: the loop over the places writes the row of y + 1 to the len cells from cur, from
the row of y in the len cells from prev. -/
theorem digitsInner_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hcur : cur + len ≤ lim.space) (hprev : prev + len ≤ cur)
    (hrow : ∀ q < len, μ (prev + q) = (placeDigit b (len - 1 - q) y : ℕ)) {x₀ : ℤ}
    (done : ∀ (c x : ℤ) (μ' : ℕ → ℤ),
      (∀ q < len, μ' (cur + q) = (placeDigit b (len - 1 - q) (y + 1) : ℕ)) →
      SameOutside μ μ' cur len → Q ⟨frame [n, b, len, dst, row, cur, prev, 0, c, x], μ'⟩)
    (hT : 26 * len + 4 ≤ T) :
    Ends lim P d digitsInner ⟨frame [n, b, len, dst, row, cur, prev, len, 1, x₀], μ⟩ T Q := by
  have h100 := std.const_le
  -- while 0 < Place
  refine Ends.whileConst (Inv μ n b len dst row cur prev y) len digitsPlace.blockCost ?start ?round
    ?done
    (by simp [digitsPlace]; omega)
  case start => exact ⟨x₀, μ, rfl, fun j hj => absurd hj (by omega), .refl⟩
  case round =>
    intro r σ hr h
    have hplace := digitsPlace_spec (P := P) (d := d) std hb hbw hcur hprev hrow hr h
    obtain ⟨x, μ', rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hplace⟩
  case done =>
    rintro _ ⟨x, μ', rfl, hcells, same⟩
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    have hdone := done (carryInto b len y) x μ' (fun q hq => ?_) same
    · simpa using hdone
    · rw [← hcells (len - 1 - q) (by omega), show len - 1 - (len - 1 - q) = q by omega]

/-! ## The loop over the rows -/












/-- **One round of the loop over the rows** writes row `i + 1`, the digits of `i + 1`, from row
`i`. -/
theorem digitsRow_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hsp : dst + n * len ≤ lim.space) (hnw : (n : ℤ) ≤ lim.word) {i : ℕ} (hi : i + 1 < n)
    {σ : State} (h : RowsDone μ n b len dst i σ) :
    Ends lim P d digitsRow σ (tRow len) (RowsDone μ n b len dst (i + 1)) := by
  obtain ⟨p, c, x, μ', rfl, hrows, same⟩ := h
  (obtain ⟨⟩ := id std)
  have hroom : (i + 1) * len + len ≤ n * len := Nat.mul_add_le_mul hi le_rfl
  have hsucc : (i + 1) * len = i * len + len := Nat.succ_mul i len
  unfold digitsRow tRow
  -- Place := len; Carry := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen len ?_ ?_ ?_);
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
          1
            -- while 0 < Place
            
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
  -- while 0 < Place
  refine Ends.next _ (digitsInner_spec (y := i) std hb hbw (by omega) (by omega)
    (fun q hq => hrows i (by omega) q hq) ?_ le_rfl)
  intro c' x' μ'' hnew same'
  -- Row := Row + 1; Prev := Cur; Cur := Cur + len
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (i + 1 + 1 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (dst + (i + 1) * len : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (dst + (i + 1 + 1) * len : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                Nat.succ_mul]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [Nat.succ_mul] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, Nat.succ_mul] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨_, _, _, _, rfl, fun y hy q hq => ?_,
      same.trans (same'.mono (by omega) (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
  · -- An earlier row lies before the cells that were written.
    have hbefore : y * len + len ≤ (i + 1) * len := Nat.mul_add_le_mul hy le_rfl
    rw [same' _ (Or.inl (by omega))]
    exact hrows y hy q hq
  · exact hnew q hq

/-- **Row 0** is zero. -/
theorem digitsZero_spec (std : Std lim) (hsp : dst + len ≤ lim.space)
    (done : Q ⟨frame [n, b, len, dst, 0, 0, 0, len], wrote μ dst (fun _ => 0) len⟩)
    (hT : 13 * len + 4 ≤ T) :
    Ends lim P d digitsZero ⟨frame [n, b, len, dst], μ⟩ T Q := by
  (obtain ⟨⟩ := id std)
  -- while Place < len
  refine Ends.whileBlock (fun q σ => σ =
    ⟨frame [n, b, len, dst, 0, 0, 0, q], wrote μ dst (fun _ => 0) q⟩) len ?start ?round ?done
  case start =>
    -- The place starts at 0.
    rw [wrote_zero, ← frame_append_zeros _ 4]
    rfl
  case round =>
    rintro q _ hq rfl
    -- mem[dst + Place] := 0; Place := Place + 1
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      by simp [update_frame_setLocal, ← wrote_succ]⟩
  case done =>
    rintro _ rfl
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), done⟩

end Digits

variable {μ : ℕ → ℤ} {n b len dst : ℕ}

/-- **digits** writes the table of digits and changes nothing else. -/
theorem digits_spec (std : Std lim) (hsp : dst + n * len ≤ lim.space) (hb : 2 ≤ b)
    (hbw : (b : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word) :
    Ends lim P d digitsBody ⟨frame [n, b, len, dst], μ⟩ (60 * ((n + 1) * (len + 1))) fun σ' =>
      (∀ x < n, SegN σ'.mem (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len))) ∧
        SameOutside μ σ'.mem dst (n * len) := by
  (obtain ⟨⟩ := id std)
  -- if 0 < n
  refine Ends.iteLast (fun hpos => ?_) fun hzero => Ends.skip
    ⟨fun x hx => absurd hx (by simp at hzero; omega), .refl⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by simp at hpos; omega⟩
  have hlen : (t + 1) * len = t * len + len := Nat.succ_mul t len
  -- Row 0.
  refine Ends.next _ (digitsZero_spec std (by omega) ?_ le_rfl) (by simp; ring_nf; omega)
  -- Row := 1; Prev := dst; Cur := dst + len, written as the invariant at i = 0 has them
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 + 1 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (dst + 0 * len : ℕ) ?_ ?_ ?_);
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
          (dst + (0 + 1) * len : ℕ)
            -- while Row < n; the n - 1 rounds take (n - 1) (26 len + 22) steps
            
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
  -- while Row < n; the n - 1 rounds take (n - 1) (26 len + 22) steps
  refine Ends.whileConst (RowsDone μ (t + 1) b len dst) t (tRow len) ?start ?round ?done
    (by simp [tRow]; ring_nf; omega)
  case start =>
    refine ⟨len, 0, 0, wrote μ dst (fun _ => 0) len, ?_, fun y hy q hq => ?_,
      sameOutside_wrote (hlen ▸ Nat.le_add_left ..)⟩
    · -- The carry and the digit start at 0.
      rw [← frame_append_zeros _ 2]
      rfl
    · obtain rfl : y = 0 := by omega
      rw [Nat.zero_mul, Nat.add_zero, wrote_done hq]
      simp [placeDigit]
  case round =>
    intro i σ hi h
    have hrow := digitsRow_spec (P := P) (d := d) std hb hbw hsp hnw (by omega) h
    obtain ⟨p, c, x, μ', rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrow⟩
  case done =>
    rintro _ ⟨p, c, x, μ', rfl, hrows, same⟩
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), fun y hy q hq => ?_, same⟩
    have hq' : q < len := by simpa [ThreeSumApsp.digitList] using hq
    rw [List.getElem_map, getElem_digitList hq']
    exact hrows y hy q hq'

/-- **The specification that the callers of digits assume.** -/
theorem digits_entry (std : Std lim) (hP : P[pDigits]? = some digitsBody) {c : ℕ} (hc : 60 ≤ c) :
    DigitsSpec lim P c :=
  fun _ _ _ _ _ hsp hb hbw hnw _ _ => .mono_const (.of_body hP (digits_spec std hsp hb hbw hnw)) hc

end Light.Sec2

end
end

section


/-!
# The table of subsets: how a row is made from the row before it

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  The programs keep them in a table.  Row number `s` of the
table is the mask `Spec.unrank L m s`, as `L` cells 1 and 0 (`bit`).  No program occurs here.

* The first row is `m` ones followed by zeros (`bit_unrank_zero`).
* Two consecutive masks are `pre 1 0 0^a 1^b` and `pre 0 1 1^b 0^a` (`Spec.unrank_succ_shape`).  So
  one pass from the end of the old row finds `b` and the length of `pre`: `scanAt` is the state of
  this scan after a number of rounds, and `scanAt_shape` is what it has found after all rounds.
* A second pass writes the new row: `newCell` is the cell that it writes (`bit_unrank_succ`), and
  the numbers that it computes on the way are small (`scanAt_fits`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec.Subsets




/-- Row 0 of the table is `m` ones followed by `L - m` zeros. -/
theorem bit_unrank_zero {L m q : ℕ} (hm : m ≤ L) (hq : q < L) :
    bit ((Spec.unrank L m 0).getD q false) = if q < m then 1 else 0 := by
  rw [Spec.unrank_zero hm]
  grind [bit]

/-- The entries of a list of the form `pre ++ x :: y :: (u^a ++ v^b)`. -/
private theorem getD_shape (pre : List Bool) (x y u v : Bool) (a b q : ℕ) :
    (pre ++ x :: y :: (List.replicate a u ++ List.replicate b v)).getD q false =
      if q < pre.length then pre.getD q false
      else if q = pre.length then x
      else if q = pre.length + 1 then y
      else if q < pre.length + 2 + a then u
      else if q < pre.length + 2 + a + b then v else false := by
  grind

/-! ## The backward scan -/





























/-- One round counts at most one more 1. -/
private theorem scanStep_ones (x q : ℤ) (S : Scan) :
    (scanStep x q S).ones = S.ones ∨ (scanStep x q S).ones = S.ones + 1 := by
  unfold scanStep
  split_ifs <;> simp

/-- After `j` rounds at most `j` ones have been counted. -/
theorem scanAt_ones_le (row : ℕ → ℤ) (L j : ℕ) :
    0 ≤ (scanAt row L j).ones ∧ (scanAt row L j).ones ≤ j := by
  induction j with
  | zero => simp [scanAt]
  | succ j ih =>
    have hstep := scanStep_ones (row (L - 1 - j)) ((L : ℤ) - 1 - (j : ℤ)) (scanAt row L j)
    rw [scanAt]
    push_cast
    omega

section shape
variable {pre : List Bool} {a b L : ℕ} {row : ℕ → ℤ} (hL : L = pre.length + 2 + a + b)
  (hrow : ∀ q < L, row q =
    bit ((pre ++ true :: false :: (List.replicate a false ++ List.replicate b true)).getD q false))
include hL hrow

/-- The cell that round `j` reads: 1 for the `b` ones at the end of the row, 0 for the `a + 1` zeros
before them, and 1 for the cell before these. -/
private theorem row_sub (j : ℕ) (hj : j ≤ b + a + 1) :
    row (L - 1 - j) = if j < b then 1 else if j < b + a + 1 then 0 else 1 := by
  rw [hrow _ (by omega), getD_shape]
  grind [bit]

/-- Phase 0: the `b` ones at the end of the row are counted. -/
private theorem scanAt_count (j : ℕ) (hj : j ≤ b) : scanAt row L j = ⟨0, j, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [scanAt, ih (by omega), row_sub hL hrow j (by omega), if_pos (by omega)]
    simp [scanStep]

/-- Phase 1: the `a + 1` zeros before the ones are passed. -/
private theorem scanAt_pass (i : ℕ) (hi : i ≤ a) : scanAt row L (b + 1 + i) = ⟨1, b, 0⟩ := by
  induction i with
  | zero =>
    rw [Nat.add_zero, scanAt, scanAt_count hL hrow b le_rfl, row_sub hL hrow b (by omega),
      if_neg (by omega), if_pos (by omega)]
    simp [scanStep]
  | succ i ih =>
    rw [← Nat.add_assoc, scanAt, ih (by omega), row_sub hL hrow _ (by omega), if_neg (by omega),
      if_pos (by omega)]
    simp [scanStep]

/-- Phase 2: the 1 before the `a + 1` zeros is found, at the position after `pre`, and from then on
the state stays as it is. -/
private theorem scanAt_found (i : ℕ) (hi : i ≤ pre.length) :
    scanAt row L (b + 1 + a + 1 + i) = ⟨2, b, pre.length⟩ := by
  induction i with
  | zero =>
    rw [Nat.add_zero, scanAt, scanAt_pass hL hrow a le_rfl, row_sub hL hrow _ (by omega),
      if_neg (by omega), if_neg (by omega),
      show (L : ℤ) - 1 - ((b + 1 + a : ℕ) : ℤ) = pre.length by omega]
    simp [scanStep]
  | succ i ih =>
    rw [← Nat.add_assoc, scanAt, ih (by omega)]
    rfl

/-- The scan of a row of the shape `pre 1 0 0^a 1^b` finds `b` and the length of `pre`. -/
private theorem scanAt_shape : scanAt row L L = ⟨2, b, pre.length⟩ := by
  rw [← scanAt_found hL hrow pre.length le_rfl]
  congr 1
  omega

end shape

/-! ## The writing pass -/





section next
variable {L m s : ℕ} (hs : s + 1 < L.choose m) {row : ℕ → ℤ}
  (hrow : ∀ q < L, row q = bit ((Spec.unrank L m s).getD q false))
include hs hrow

/-- **From one row to the next.**  If row number `s` has a successor, the cells of row `s + 1` are
given by `newCell`, from the cells of row `s` and the result of its scan. -/
theorem bit_unrank_succ {q : ℕ} (hq : q < L) :
    bit ((Spec.unrank L m (s + 1)).getD q false) = newCell (scanAt row L L) (row q) q := by
  obtain ⟨pre, a, b, hL, hthis, hnext⟩ := Spec.unrank_succ_shape hs
  rw [hthis] at hrow
  rw [scanAt_shape hL hrow, hrow q hq, hnext, getD_shape, getD_shape, newCell]
  dsimp only
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The result of the scan of a row that has a successor fits into a row. -/
theorem scanAt_fits : (scanAt row L L).Fits L := by
  obtain ⟨pre, a, b, hL, hthis, -⟩ := Spec.unrank_succ_shape hs
  rw [hthis] at hrow
  rw [scanAt_shape hL hrow, Scan.Fits]
  dsimp only
  omega

end next

end ThreeSumApsp.Spec.Subsets

end
end

section


/-!
# The table of subsets

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  Section 2.4.4 counts the time to "list the K₀² subsets".
subsets(L, m, KK, mask), which is called with KK = K₀², writes the first KK masks of the enumeration
`Spec.unrank`, one after the other, as 0/1 cells from mask.  Row 0 is m ones followed by zeros
(`firstRow_spec`).  Each further row is made from the row before it: one pass from the end of the
old row finds the last 1 that is followed by a 0 (`scan_spec`), and one pass writes the new row
(`write_spec`).  There is no arithmetic on the entries, and a row takes O(L) steps.  What the two
passes compute is described without a program by `scanAt` and `newCell`, with the facts
`bit_unrank_succ` and `scanAt_fits`; here each pass is connected with this description,
`tableRow_spec` treats one row, and `subsetTable_spec` runs through the rows.  `subsets_entry` is
the specification that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp.Spec.Subsets

namespace Light.Sec2.Subsets

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

























































/-! ## The three passes -/












variable {μ : ℕ → ℤ} {L m KK mask s a : ℕ} {S : Scan} {j₀ : ℤ} {T : ℕ} {Q : State → Prop}

/-- **The first row**: the pass writes m ones and then zeros to the L cells from a. -/
theorem firstRow_spec (std : Std lim) (ha : a + L ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a S L), wrote μ a (fun r => if r < m then 1 else 0) L⟩)
    (hT : 17 * L + 6 ≤ T) :
    Ends lim P d firstRowLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  (obtain ⟨⟩ := id std)
  -- for Cell < L
  refine Ends.forFrame (fun j μ' => μ' = wrote μ a (fun r => if r < m then 1 else 0) j) L
    wrote_zero.symm ?round (fun μ' h => h ▸ done) (hT := by simp [firstRowRound]; omega)
  rintro j _ hj rfl
  unfold firstRowRound
  -- if Cell < m then mem[Addr + Cell] := 1 else mem[Addr + Cell] := 0
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · focus
       ((((first
               | refine Light.Ends.seqSelf ?_
               | refine Light.Ends.skipLast ?_));
           (repeat
               with_unfolding_none
                 first
                 | refine Light.Ends.seqAssoc ?_
                 | refine Light.Ends.skipThen ?_)));
       (refine Light.Ends.storeToThen (a + j) 1 ?_ ?_ ?_);
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
    exact ⟨rfl, by rw [← wrote_succ, if_pos (by simpa using hc)]⟩
  · focus
       ((((first
               | refine Light.Ends.seqSelf ?_
               | refine Light.Ends.skipLast ?_));
           (repeat
               with_unfolding_none
                 first
                 | refine Light.Ends.seqAssoc ?_
                 | refine Light.Ends.skipThen ?_)));
       (refine Light.Ends.storeToThen (a + j) 0 ?_ ?_ ?_);
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
    exact ⟨rfl, by rw [← wrote_succ, if_neg (by simpa using hc)]⟩

/-- One round of the scan does to the local variables what `scanStep` says of the cell number j from
the end of the row of L cells that ends just before the address a. -/
theorem scanRound_runs (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space) {j : ℕ} (hj : j < L)
    (hones : 0 ≤ S.ones ∧ S.ones ≤ j) :
    scanRound.Runs lim ⟨frame (locals L m KK mask s a S j), μ⟩ fun σ' => σ' =
      ⟨frame (locals L m KK mask s a (scanStep (μ (a - 1 - j)) ((L : ℤ) - 1 - j) S) j), μ⟩ := by
  (obtain ⟨⟩ := id std)
  have haddr : ((a : ℤ) - 1 - j).toNat = a - 1 - j := by omega
  unfold scanRound scanStep
  by_cases hcount : S.phase < 1
  · -- Phase 0: a zero ends the counting, a one is counted.
    rw [if_pos hcount]
    refine .ite_pos ?_
    by_cases hx : μ (a - 1 - j) < 1
    · rw [if_pos hx]
      exact .ite_pos ⟨by (((try have := Light.Std.space_le (by assumption)));
                             ((try have := Light.Std.const_le (by assumption)));
                             (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
    · rw [if_neg hx]
      exact .ite_neg ⟨by (((try have := Light.Std.space_le (by assumption)));
                             ((try have := Light.Std.const_le (by assumption)));
                             (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
  · rw [if_neg hcount]
    refine .ite_neg ?_
    by_cases hpass : S.phase < 2
    · -- Phase 1: a zero is passed, a one is what the scan looks for.
      rw [if_pos hpass]
      refine .ite_pos ?_
      by_cases hx : μ (a - 1 - j) < 1
      · rw [if_pos hx]
        exact .ite_pos ⟨trivial, rfl⟩ (by simpa [haddr] using hx)
      · rw [if_neg hx]
        exact .ite_neg ⟨by (((try have := Light.Std.space_le (by assumption)));
                               ((try have := Light.Std.const_le (by assumption)));
                               (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
    · -- Phase 2: nothing is left to do.
      rw [if_neg hpass]
      exact .ite_neg ⟨trivial, rfl⟩

/-- **The scan** of the row of L cells that ends just before the address a changes no cell and
leaves its result in the local variables. -/
theorem scan_spec (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L), μ⟩)
    (hT : 33 * L + 12 ≤ T) :
    Ends lim P d scanLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  (obtain ⟨⟩ := id std)
  -- Phase := 0; Ones := 0; Pos := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
          0
            -- for Cell < L
            
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
  -- for Cell < L
  refine Ends.for (fun j σ =>
      σ = ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L j) j), μ⟩)
    L _ ?start (fun j σ hj _ hσ => Ends.block ?round le_rfl) ?done ?bound
    (hT := by simp [scanRound]; omega)
  case start => simp [update_frame_setLocal, scanAt]
  case round =>
    subst hσ
    refine (scanRound_runs std hLa ha hj (scanAt_ones_le _ L j)).mono ?_
    rintro _ rfl
    rw [scanAt, prevRow, show a - L + (L - 1 - j) = a - 1 - j by omega]
    simp [update_frame_setLocal]
  case done => exact fun _ _ h => h ▸ done
  case bound => exact fun j _ _ _ h => h ▸ by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))

/-- **The writing pass** writes the new row to the L cells from a, from the row of L cells before
it and the result S of the scan. -/
theorem write_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hS : S.Fits L) (done : Q ⟨frame (locals L m KK mask s a S L), wrote μ a (newRow μ a L S) L⟩)
    (hT : 31 * L + 6 ≤ T) :
    Ends lim P d writeLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  (obtain ⟨⟩ := id std)
  unfold Scan.Fits at hS
  -- for Cell < L
  refine Ends.forFrame (fun j μ' => μ' = wrote μ a (newRow μ a L S) j) L wrote_zero.symm
    ?round (fun μ' h => h ▸ done) (hT := by simp [writeRound]; omega)
  rintro j _ hj rfl
  -- The cell of the old row has not been overwritten.
  have haddr : ((a : ℤ) - L + j).toNat = a - L + j := by omega
  have hold : wrote μ a (newRow μ a L S) j (a - L + j) = μ (a - L + j) :=
    wrote_rest (Or.inl (by omega))
  unfold writeRound
  rw [← wrote_succ, newRow, newCell]
  -- if Cell < Pos then mem[Addr + Cell] := mem[Addr - L + Cell] else if Cell < Pos + 1 then 0
  -- else if Cell < Pos + 2 + Ones then 1 else 0: the four cases of newCell
  refine Ends.iteLast (fun c₁ => ?_) fun c₁ => Ends.iteLast (fun c₂ => ?_) fun c₂ =>
    Ends.iteLast (fun c₃ => ?_) fun c₃ => ?_
  · focus
       ((((first
               | refine Light.Ends.seqSelf ?_
               | refine Light.Ends.skipLast ?_));
           (repeat
               with_unfolding_none
                 first
                 | refine Light.Ends.seqAssoc ?_
                 | refine Light.Ends.skipThen ?_)));
       (refine Light.Ends.storeToThen (a + j) (μ (a - L + j)) ?_ ?_ ?_);
       (on_goal -1 =>
           first
           |
             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                   hold]);
               (first
                 | omega
                 | ((ring_nf); (omega))))
           | omega
           |
             (simp [haddr, hold] <;>
                 first
                 | omega
                 | ((ring_nf); (omega))));
       (on_goal -1 =>
           (((try have := Light.Std.space_le (by assumption)));
             ((try have := Light.Std.const_le (by assumption)));
             (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hold] <;> omega)));
       (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨rfl, by rw [if_pos (by simpa using c₁)]⟩
  · focus
       ((((first
               | refine Light.Ends.seqSelf ?_
               | refine Light.Ends.skipLast ?_));
           (repeat
               with_unfolding_none
                 first
                 | refine Light.Ends.seqAssoc ?_
                 | refine Light.Ends.skipThen ?_)));
       (refine Light.Ends.storeToThen (a + j) 0 ?_ ?_ ?_);
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
    exact ⟨rfl, by rw [if_neg (by simpa using c₁), if_pos (by simpa using c₂)]⟩
  · focus
       ((((first
               | refine Light.Ends.seqSelf ?_
               | refine Light.Ends.skipLast ?_));
           (repeat
               with_unfolding_none
                 first
                 | refine Light.Ends.seqAssoc ?_
                 | refine Light.Ends.skipThen ?_)));
       (refine Light.Ends.storeToThen (a + j) 1 ?_ ?_ ?_);
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
    exact ⟨rfl, by
      rw [if_neg (by simpa using c₁), if_neg (by simpa using c₂), if_pos (by simpa using c₃)]⟩
  · focus
       ((((first
               | refine Light.Ends.seqSelf ?_
               | refine Light.Ends.skipLast ?_));
           (repeat
               with_unfolding_none
                 first
                 | refine Light.Ends.seqAssoc ?_
                 | refine Light.Ends.skipThen ?_)));
       (refine Light.Ends.storeToThen (a + j) 0 ?_ ?_ ?_);
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
    exact ⟨rfl, by
      rw [if_neg (by simpa using c₁), if_neg (by simpa using c₂), if_neg (by simpa using c₃)]⟩

/-- **A further row**: the two passes write the new row to the L cells from a, from the row of L
cells before it, if the result of the scan leaves room. -/
theorem nextRow_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hroom : (scanAt (prevRow μ a L) L L).Fits L)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L),
      wrote μ a (newRow μ a L (scanAt (prevRow μ a L) L L)) L⟩)
    (hT : 64 * L + 18 ≤ T) :
    Ends lim P d nextRow ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q :=
  Ends.next _ (scan_spec std hLa (by omega) (write_spec std hLa ha hroom done (by omega)) le_rfl)

/-! ## The loop over the rows -/










/-- The end of a round: row number s has been written, and the number and the address of the row
move on. -/
private theorem rowDone_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space)
    (hKK : (KK : ℤ) ≤ lim.word) (hs : s < KK) {μ' : ℕ → ℤ} {f : ℕ → ℤ} {j : ℤ}
    (hrows : ∀ t < s, SegB μ' (mask + t * L) (Spec.unrank L m t))
    (same : SameOutside μ μ' mask (KK * L))
    (hf : ∀ r < L, f r = bit ((Spec.unrank L m s).getD r false))
    (hT : 8 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.set Row ((Light.Expr.op Light.Op.add) (v Row) (k 1)))
                    (.set Addr ((Light.Expr.op Light.Op.add) (v Addr) (v Levels)))))
      ⟨frame (locals L m KK mask s (mask + s * L) S j), wrote μ' (mask + s * L) f L⟩ T
      (RowsDone μ L m KK mask (s + 1)) := by
  (obtain ⟨⟩ := id std)
  have hroom : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  -- Row := Row + 1; Addr := Addr + L
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (s + 1 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (mask + (s + 1) * L : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                Nat.succ_mul]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [Nat.succ_mul] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, Nat.succ_mul] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨S, j, _, rfl, fun t ht => ?_,
      same.trans ((sameOutside_wrote le_rfl).mono (by omega) (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
  · -- An earlier row lies before the cells that were written.
    have hbefore : t * L + L ≤ s * L := Nat.mul_add_le_mul ht le_rfl
    refine Seg.of_sameOutside (hrows t ht) (sameOutside_wrote le_rfl) (Or.inl ?_)
    rw [List.length_map, Spec.length_unrank]
    omega
  · -- The new row.
    intro r hr
    rw [List.length_map, Spec.length_unrank] at hr
    rw [wrote_done hr, hf r hr, List.getElem_map,
      List.getD_eq_getElem _ _ (by rwa [Spec.length_unrank])]
    rfl

/-- **One round of the loop over the rows** writes row number `s`, the mask number `s`. -/
theorem tableRow_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) (hs : s < KK) {σ : State}
    (h : RowsDone μ L m KK mask s σ) :
    Ends lim P d tableRow σ (tRow L) (RowsDone μ L m KK mask (s + 1)) := by
  obtain ⟨S, j, μ', rfl, hrows, same⟩ := h
  (obtain ⟨⟩ := id std)
  push_cast at hKL
  have hroom : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  unfold tableRow tRow
  -- if Row < 1
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · -- The first row.
    obtain rfl : s = 0 := by simp at hc; omega
    refine Ends.next _ (firstRow_spec std (by omega) ?_ le_rfl)
    exact rowDone_spec std hmask (by omega) hs hrows same fun r hr => (bit_unrank_zero hm hr).symm
  · -- A further row, from the row before it.
    obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by simp at hc; omega⟩
    have hsucc : (p + 1) * L = p * L + L := Nat.succ_mul p L
    have hprev : ∀ q < L, prevRow μ' (mask + (p + 1) * L) L q
        = bit ((Spec.unrank L m p).getD q false) := fun q hq => by
      rw [prevRow, show mask + (p + 1) * L - L + q = mask + p * L + q by omega]
      exact SegB.get (hrows p (by omega)) (by rwa [Spec.length_unrank])
    have hnext : p + 1 < L.choose m := by omega
    refine Ends.next _ (nextRow_spec std (by omega) (by omega) (scanAt_fits hnext hprev) ?_ le_rfl)
    exact rowDone_spec std hmask (by omega) hs hrows same fun r hr =>
      (bit_unrank_succ hnext hprev hr).symm

/-- **subsets** writes the table and changes nothing else. -/
theorem subsetTable_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d subsetTableBody ⟨frame [L, m, KK, mask], μ⟩ (64 * ((KK + 1) * (L + 1))) fun σ' =>
      (∀ s < KK, SegB σ'.mem (mask + s * L) (Spec.unrank L m s)) ∧
        SameOutside μ σ'.mem mask (KK * L) := by
  (obtain ⟨⟩ := id std)
  -- Row := 0; Addr := mask
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen mask ?_ ?_ ?_);
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
  -- while Row < KK; the KK rounds take KK (64 L + 34) steps
  refine Ends.whileConst (RowsDone μ L m KK mask) KK (tRow L) ?start ?round ?done
    (by simp [tRow]; ring_nf; omega)
  case start =>
    refine ⟨⟨0, 0, 0⟩, 0, μ, ?_, fun t ht => absurd ht (by omega), .refl⟩
    -- The state of the scan and the counter of the inner loops start at 0.
    simp only [setLocal, Nat.zero_mul, Nat.add_zero]
    rw [← frame_append_zeros _ 4]
    rfl
  case round =>
    intro s σ hs h
    have hrow := tableRow_spec (P := P) (d := d) std hmask hm hKK hKL hs h
    obtain ⟨S, j, μ', rfl, -⟩ := h
    push_cast at hKL
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrow⟩
  case done =>
    rintro _ ⟨S, j, μ', rfl, hrows, same⟩
    push_cast at hKL
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrows, same⟩

end Light.Sec2.Subsets

namespace Light.Sec2

open ThreeSumApsp Subsets

variable {lim : Limits} {P : Program}

/-- **The specification that the callers of subsets assume.** -/
theorem subsets_entry (std : Std lim) (hP : P[pSubsets]? = some subsetTableBody) {c : ℕ}
    (hc : 64 ≤ c) : SubsetsSpec lim P c :=
  fun _ _ _ _ _ hmask hm hKK hKL _ _ =>
    .mono_const (.of_body hP (subsetTable_spec std hmask hm hKK hKL)) hc

end Light.Sec2

end
end

section


/-!
# Theorem 5: the program

The list of the procedures of Theorem 5's program, in the order of their numbers.  An entry is the
specification of a procedure together with a bound on its time, a constant times a shape.  In every
program that begins with this list, the procedures that the shared stage calls meet their entries
with the constant cShared5 (sharedCallees_of_prefix), and those that the solver calls with the
constant cMain5 (mainCallees_of_prefix).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.WordRam











/-- A procedure of program5 is a procedure, with the same number, of every program that begins with
program5. -/
theorem at_prefix {p : ℕ} {body : Stmt} (h : program5[p]? = some body) (R : Program) :
    (program5 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-! ## All entries -/







/-- The procedures that the shared stage calls meet their entries. -/
theorem sharedCallees_of_prefix_sourceProof (R : Program) (lim : Limits) (std : Std lim) :
    SharedCallees lim (program5 ++ R) cShared5 where
  pow := pow_entry std (at_prefix rfl R) (by decide)
  binom := binom_entry std (at_prefix rfl R) (by decide)
  sqrt := sqrt_entry (at_prefix rfl R) (by decide)
  coef := coef_entry std (at_prefix rfl R) (by decide)
  subsets := subsets_entry std (at_prefix rfl R) (by decide)
  counters := counters_entry std (at_prefix rfl R) (by decide)
  digits := digits_entry std (at_prefix rfl R) (by decide)
  bandsL := encodeBandsL_entry std (at_prefix rfl R) (bandArrayL_entry std (at_prefix rfl R))
    (encodeL_entry std (at_prefix rfl R) (at_prefix rfl R)) (by decide)
  bandsR := encodeBandsR_entry std (at_prefix rfl R) (bandArrayR_entry std (at_prefix rfl R))
    (encodeR_entry std (at_prefix rfl R) (at_prefix rfl R)) (by decide)














end Light.Sec2

end
end


theorem solution : ∀ (R : Light.Program) (lim : Light.Limits),
  Light.Std lim →
    Light.Sec2.SharedCallees lim
      (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
        (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) Light.Sec2.program5 R)
      Light.Sec2.cShared5 := by
  exact @Light.Sec2.sharedCallees_of_prefix_sourceProof

#print axioms solution
