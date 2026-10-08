-- Prove2me | solution 1 for Light.Sec4.specs40
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:28:43.761031+00:00
-- url     : https://prove2.me/submissions/428624bb-2b0c-46dd-824f-fd12ab9e9001

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
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Boxes
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_BoxesFromLeaves
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Lemma27_28
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Cubes
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineScan
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
import Mathlib.Data.List.Iterate
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
import Theorems.Thm_ThreeSumApsp_Spec_TrieRep_insert
import Theorems.Thm_ThreeSumApsp_Spec_abs_dpValue_le
import Theorems.Thm_ThreeSumApsp_Spec_mem_nineStrs
import Theorems.Thm_ThreeSumApsp_Spec_pairwise_lt_nineStrs
import Theorems.Thm_ThreeSumApsp_eq_lowest_of_lt
import Theorems.Thm_ThreeSumApsp_getD_weaveList
import Theorems.Thm_ThreeSumApsp_lemma_29_split

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

/-- An assignment at the end of the program. -/
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by (((try have := Light.Std.space_le (by assumption)));
                                           ((try have := Light.Std.const_le (by assumption)));
                                           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : e.cost + 1 ≤ T := by first
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
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h
























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

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by (((try have := Light.Std.space_le (by assumption)));
                                                       ((try have := Light.Std.const_le (by assumption)));
                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : c.cost + 1 ≤ T := by first
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
                                       | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

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





/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)

/-- Writing a cell that need not be kept. -/
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc

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

/-- The first `i + 1` entries are the first `i` entries and entry `i`. -/
theorem take_succ_getD (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_add_one, List.getD_eq_getElem l d hi, List.getElem?_eq_getElem hi,
    Option.toList_some]

/-! ## Blocks one after the other -/











































































/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl

/-- Partial sums of natural numbers grow. -/
theorem sum_map_range_mono (g : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- One more term of a partial sum; beyond the end of the list the term is `0`. Within the list,
`List.sum_take_succ` has `l[j]` in place of `l.getD j 0`. -/
theorem sum_take_succ_getD {M : Type*} [AddMonoid M] (l : List M) (j : ℕ) :
    (l.take (j + 1)).sum = (l.take j).sum + l.getD j 0 := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.sum_take_succ l j hj, List.getD_eq_getElem l 0 hj]
  · rw [List.getD_eq_default l 0 hj, List.take_of_length_le hj,
      List.take_of_length_le (Nat.le_succ_of_le hj), add_zero]

/-- One more term of a partial sum of the table `f 0, …, f (n - 1)`. -/
theorem sum_take_map_range_succ {M : Type*} [AddMonoid M] (f : ℕ → M) {n j : ℕ} (hj : j < n) :
    (((List.range n).map f).take (j + 1)).sum = (((List.range n).map f).take j).sum + f j := by
  rw [sum_take_succ_getD, getD_map_range f hj]














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

/-- If `|f x| ≤ B` for all `x ∈ l`, then every initial part of the numbers `f x` has a sum of
absolute value at most `l.length * B`. -/
theorem abs_sum_take_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) (k : ℕ) :
    |((l.map f).take k).sum| ≤ l.length * B := by
  refine (List.abs_sum_take_le_sum_abs _ k).trans ?_
  simpa using List.sum_le_card_nsmul ((l.map f).map fun x => |x|) B (by simpa using h)




























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












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)












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

theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']





/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_52066_0 apspMacro_52066_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_52066_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_52066_2 apspMacro_52066_0 (by omega)));
                                                                                                  (revert apspMacro_52066_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_52066_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_52066_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_52066_3 apspMacro_52066_0 (by omega)));
                                                                                                  (revert apspMacro_52066_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_52066_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_52066_4 apspMacro_52066_0 (by omega)));
                                                                                                  (revert apspMacro_52066_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

/-- Writing into a segment. -/
theorem Seg.update_in (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (x : ℤ) :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  intro j hj
  have hj' : j < l.length := by simpa using hj
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne (by omega), List.getElem_set_of_ne (by omega), h j hj']

/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)

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

/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)

/-- One more entry of a list of natural numbers is written behind its first k entries. -/
theorem SegN.take_succ {l : List ℕ} {k : ℕ} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) ((l.getD k 0 : ℕ) : ℤ)) a (l.take (k + 1)) := by
  have hsnoc := h.snoc (l.getD k 0)
  rwa [List.length_take, Nat.min_eq_left hk.le, ← List.take_succ_getD l hk 0] at hsnoc






/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_55416_0 apspMacro_55416_1);
                                                    (first
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_55416_2));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_55416_2 apspMacro_55416_0 (by omega)));
                                                                    (revert apspMacro_55416_2)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((simp [] at apspMacro_55416_1);
                                                          (((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_55416_3));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_55416_3 apspMacro_55416_0 (by omega)));
                                                                    (revert apspMacro_55416_3)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_55416_4));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_55416_4 apspMacro_55416_0 (by omega)));
                                                                    (revert apspMacro_55416_4)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (fail
                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                        its condition K x does not follow from the hypotheses."))))) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)

/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simpa using hd)





































end Light

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




















































/-! ### Linear forms as polynomials -/























































/-! ### Lemma 6 -/



































/-! ### Which terms contribute to which output variables -/












/-- The second observation in one statement: a term contributes to `z` if and only if `z` is inner,
that is `z₀`, or the term is `z.privateTerm`, which is `P_ij` for `z = z_ij`. (This is the term that
the private leaf of Section 2.4.3 has at a level with the variable `z`.) -/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert


















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











/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/
































/-- The code of a vertex at depth `n` is less than `10^n`. -/
theorem codeT_lt {n : ℕ} (τ : Vertex n) : codeT τ < 10 ^ n :=
  codeStr_lt termEquiv τ

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





















/-! ## The coefficients of the linear forms, as tables -/







































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

























/-- A mask of the enumeration has `L - m` entries `false`. -/
theorem count_false_unrank {L m r : ℕ} (hr : r < L.choose m) :
    (unrank L m r).count false = L - m := by
  have hall := List.count_not_add_count (unrank L m r) true
  rw [count_unrank hr, length_unrank, Bool.not_true] at hall
  omega


























/-! ## Masks and sets of levels -/


















































/-! ## From one mask to the next -/











































































end ThreeSumApsp.Spec

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
































end

/-! ## Counting the levels of a set below a level -/








/-! ## The code of a glued string -/



































/-! ## The digits and the code of the output string of a position -/

section outDigits
variable {m ℓ : ℕ} {mask : List Bool} {rI rJ : List ℕ}







/-- An output string has one digit for each level. -/
@[simp] theorem length_outDigits : (outDigits m mask rI rJ).length = mask.length :=
  length_weaveList ..

/-- The digit at a level of the inner set is 9. -/
theorem getD_outDigits_of_true (hm : mask.count true = m) (hℓ : ℓ < mask.length)
    (hb : mask.getD ℓ false = true) : (outDigits m mask rI rJ).getD ℓ 0 = 9 := by
  have hlt := List.count_take_lt hℓ false hb
  rw [outDigits, getD_weaveList, if_pos hℓ, if_pos hb,
    List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega), List.getElem_replicate]

/-- The digit at a level outside the inner set is `3 x + y` for the next digits `x` of the row and
`y` of the column. -/
theorem getD_outDigits_of_false (hI : rI.length = mask.count false)
    (hJ : rJ.length = mask.count false) (hℓ : ℓ < mask.length) (hb : mask.getD ℓ false = false) :
    (outDigits m mask rI rJ).getD ℓ 0
      = 3 * rI.getD ((mask.take ℓ).count false) 0 + rJ.getD ((mask.take ℓ).count false) 0 := by
  have hlt := List.count_take_lt hℓ false hb
  rw [outDigits, getD_weaveList, if_pos hℓ, if_neg (by rw [hb]; exact Bool.false_ne_true),
    List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]














end outDigits



















































/-! ## The codes of the left and right strings, and the input arrays of the bands -/





























































section
variable {L m N : ℕ} (hmL : m ≤ L)









































end




















































end ThreeSumApsp.Spec

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




















/-! ### The counts -/



























































































































































































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
























/-! ### A leaf as a cube without stars (Section 4.2) -/
























/-! ### Replacing a star by a term (proof of Lemma 29) -/
































/-! ### Putting stars into a leaf (Section 4.2) -/










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







/-- `V` is a set of levels of `Q`. -/
theorem Vof_subset (m t : ℕ) {Q Z : Finset (Fin L)} (hZ : Z ⊆ Q) : Vof m t Q Z ⊆ Q :=
  union_subset hZ ((lowest_subset _ _).trans sdiff_subset)










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








































































end BV































































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












/-- Section 4.2: "When V is the set defined above from a leaf τ, the box of τ is the one in 𝓑_V with
the terms of τ at the levels of Q ∖ V": it is a cube of `𝓑_V`, for the set `V` of `τ`. -/
theorem boxOfLeaf_mem_BV (m t : ℕ) {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    boxOfLeaf m t η τ ∈ BV η (Vof m t (innerSetO η) (Zof (innerSetO η) τ)) :=
  starAt_mem_BV hτ
    ((sdiff_FV_subset_iff (Vof_subset m t (Zof_subset _ τ))).2 (Vof_sdiff_lt m t _ _))
    subset_union_left


























/-! ### Figure 10 -/
































/-! ### Lemma 27 -/





















/-! ### Lemma 28 -/



















































































































































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


end

theorem digitsC_injective (L : ℕ) : Function.Injective (digitsC : Cube L → List ℕ) :=
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








theorem starFirst_zero (l : List ℕ) : starFirst 0 l = l := by
  cases l <;> rfl

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

/-- There is no string with more nines than digits, or if the bounds contradict each other. -/
private theorem nineStrs_eq_nil {n lo hi : ℕ} (h : n < lo ∨ hi < lo) : nineStrs n lo hi = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro l hl
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have hcount := List.count_le_length (a := 9) (l := l)
  omega




























theorem nineStrs_nodup (n lo hi : ℕ) : (nineStrs n lo hi).Nodup :=
  (pairwise_lt_nineStrs n lo hi).imp fun h => ne_of_lt h

/-! ## The length of the list -/







































































/-! ## The first string -/

/-- If there is a string at all, the bounds are consistent. -/
private theorem le_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    lo ≤ n ∧ lo ≤ hi := by
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have hcount := List.count_le_length (a := 9) (l := l)
  omega

/-- The least string begins with 0 if not all digits have to be nines. -/
private theorem nineFirst_succ {n lo : ℕ} (h : lo ≤ n) :
    nineFirst (n + 1) lo = 0 :: nineFirst n lo := by
  rw [nineFirst, nineFirst, Nat.succ_sub h, List.replicate_succ, List.cons_append]

/-- The string of nines. -/
private theorem nineFirst_self_succ (n : ℕ) : nineFirst (n + 1) (n + 1) = 9 :: nineFirst n n := by
  simp [nineFirst, List.replicate_succ]

/-- Without strings of n digits there are no strings of n + 1 digits that begin below 9. -/
private theorem flatMap_map_nil (l : List ℕ) :
    l.flatMap (fun d => ([] : List (List ℕ)).map (d :: ·)) = [] :=
  List.flatMap_eq_nil_iff.2 fun _ _ => rfl

theorem headOpt_nineStrs {n lo hi : ℕ} (h : lo ≤ n) (h' : lo ≤ hi) :
    (nineStrs n lo hi).head? = some (nineFirst n lo) := by
  induction n generalizing lo hi with
  | zero =>
    obtain rfl : lo = 0 := by omega
    rfl
  | succ n ih =>
    rw [nineStrs]
    rcases Nat.lt_or_ge n lo with hlo | hlo
    · -- all digits are nines
      obtain rfl : lo = n + 1 := by omega
      rw [nineStrs_eq_nil (Or.inl (Nat.lt_succ_self n)), if_neg (by omega), flatMap_map_nil,
        List.nil_append, List.head?_map, Nat.add_sub_cancel, ih le_rfl (by omega),
        nineFirst_self_succ]
      rfl
    · rw [List.range_succ_eq_map, List.flatMap_cons, List.append_assoc, List.head?_append,
        List.head?_map, ih hlo h', nineFirst_succ hlo]
      rfl

/-! ## From each string to the next -/






/-- f goes through two lists one after the other exactly if it goes through both, and from the last
member of the first list to the first member of the second (to z if the second list is empty). -/
private theorem nextTo_append {α : Type} {f : α → Option α} {A B : List α} {z : Option α} :
    NextTo f (A ++ B) z ↔ NextTo f A (B.head?.or z) ∧ NextTo f B z := by
  induction A with
  | nil => simp [NextTo]
  | cons x A ih =>
    rw [List.cons_append, NextTo, NextTo, ih, List.head?_append, Option.or_assoc, and_assoc]

/-- What `NextTo` says about the member number i. -/
private theorem NextTo.getElem {α : Type} {f : α → Option α} {A : List α} {z : Option α}
    (h : NextTo f A z) (i : ℕ) (hi : i < A.length) : f A[i] = A[i + 1]?.or z := by
  induction A generalizing i with
  | nil => simp at hi
  | cons x A ih =>
    cases i with
    | zero => rw [List.getElem_cons_zero, h.1, List.getElem?_cons_succ, List.head?_eq_getElem?]
    | succ i =>
      rw [List.getElem_cons_succ, List.getElem?_cons_succ]
      exact ih h.2 i (by simpa using hi)

/-- The block of the strings with the first digit d. -/
private theorem nextTo_map_cons (lo hi n d : ℕ) (S : List (List ℕ)) (hS : ∀ l ∈ S, l.length = n)
    (h : NextTo (nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi)) S none) :
    NextTo (nineNext lo hi) (S.map (d :: ·)) (nineRaise lo hi n d) := by
  induction S with
  | nil => trivial
  | cons x r ih =>
    refine ⟨?_, ih (fun l hl => hS l (by simp [hl])) h.2⟩
    rw [nineNext, h.1, Option.or_none]
    rcases r with _ | ⟨y, r⟩
    · simp only [List.head?_nil, List.map_nil, Option.none_or, hS x (by simp)]
    · rfl







section

variable {n lo hi : ℕ}

/-- `nineNext` goes through the last block, the strings with the first digit 9. -/
private theorem nextTo_nineBlocks_zero (a : ℕ)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) :
    NextTo (nineNext lo hi) (nineBlocks n lo hi a 0) none := by
  rw [nineBlocks, List.range'_zero, List.flatMap_nil, List.nil_append]
  split_ifs
  · trivial
  · exact nextTo_map_cons lo hi n 9 _ (fun _ => length_of_mem_nineStrs) h9

/-- The first string after the block with the first digit a is the one to which `nineNext` goes by
raising the digit a. -/
private theorem head_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi) {a k : ℕ} (hak : a + 1 + k = 9) :
    (nineBlocks n lo hi (a + 1) k).head? = nineRaise lo hi n a := by
  rw [nineBlocks, nineRaise]
  cases k with
  | zero =>
    obtain rfl : a = 8 := by omega
    rw [List.range'_zero, List.flatMap_nil, List.nil_append]
    by_cases h0 : hi = 0
    · simp [h0]
    · rw [if_neg h0, List.head?_map, headOpt_nineStrs (by omega) (by omega), if_neg (lt_irrefl 8),
        if_pos ⟨rfl, Nat.pos_of_ne_zero h0⟩]
      rfl
  | succ k =>
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, List.head?_append, List.head?_map,
      headOpt_nineStrs hn hh, if_pos (show a < 8 by omega)]
    rfl

/-- `nineNext` goes through the blocks. -/
private theorem nextTo_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi)
    (h : NextTo (nineNext lo hi) (nineStrs n lo hi) none)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) (k a : ℕ)
    (hak : a + k = 9) : NextTo (nineNext lo hi) (nineBlocks n lo hi a k) none := by
  induction k generalizing a with
  | zero => exact nextTo_nineBlocks_zero a h9
  | succ k ih =>
    have hsplit : nineBlocks n lo hi a (k + 1)
        = (nineStrs n lo hi).map (a :: ·) ++ nineBlocks n lo hi (a + 1) k := by
      rw [nineBlocks, nineBlocks, List.range'_succ, List.flatMap_cons, List.append_assoc]
    rw [hsplit, nextTo_append, Option.or_none, head_nineBlocks hn hh (by omega)]
    refine ⟨nextTo_map_cons lo hi n a _ (fun _ => length_of_mem_nineStrs) ?_, ih (a + 1) (by omega)⟩
    rwa [if_neg (by omega), if_neg (by omega)]

end

/-- `nineNext` goes through the list. -/
private theorem nextTo_nineStrs (n lo hi : ℕ) :
    NextTo (nineNext lo hi) (nineStrs n lo hi) none := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs
    · exact ⟨rfl, trivial⟩
    · trivial
  | succ n ih =>
    by_cases h : lo ≤ n ∧ lo ≤ hi
    · rw [nineStrs, List.range_eq_range']
      exact nextTo_nineBlocks h.1 h.2 (ih lo hi) (ih _ _) 9 0 rfl
    · -- only strings that begin with a nine
      rw [nineStrs, nineStrs_eq_nil (by omega), flatMap_map_nil]
      exact nextTo_nineBlocks_zero 0 (ih _ _)

/-- `nineNext` goes from each string of the list to the following one, and from the last one to
none. -/
theorem nineNext_getElem (n lo hi i : ℕ) (h : i < (nineStrs n lo hi).length) :
    nineNext lo hi ((nineStrs n lo hi)[i]) = (nineStrs n lo hi)[i + 1]? := by
  rw [(nextTo_nineStrs n lo hi).getElem i h, Option.or_none]

section

variable {n lo hi i : ℕ}

theorem nineStr_succ (n lo hi i : ℕ) :
    nineStr n lo hi (i + 1) = (nineNext lo hi (nineStr n lo hi i)).getD (nineStr n lo hi i) :=
  Function.iterate_succ_apply' _ _ _

/-- `nineStr n lo hi i` is the member number i of the list. -/
theorem getElem_nineStrs (h : i < (nineStrs n lo hi).length) :
    (nineStrs n lo hi)[i] = nineStr n lo hi i := by
  induction i with
  | zero =>
    obtain ⟨hn, hh⟩ := le_of_mem_nineStrs (List.getElem_mem h)
    refine Option.some.inj ?_
    rw [← List.getElem?_eq_getElem h, ← List.head?_eq_getElem?, headOpt_nineStrs hn hh]
    rfl
  | succ i ih =>
    rw [nineStr_succ, ← ih (Nat.lt_of_succ_lt h), nineNext_getElem, List.getElem?_eq_getElem h]
    rfl

theorem nineStr_mem (h : i < (nineStrs n lo hi).length) : nineStr n lo hi i ∈ nineStrs n lo hi :=
  getElem_nineStrs h ▸ List.getElem_mem h

/-- There is a next string exactly if the string is not the last one of the list. -/
theorem isSome_nineNext_nineStr (h : i < (nineStrs n lo hi).length) :
    (nineNext lo hi (nineStr n lo hi i)).isSome = decide (i + 1 < (nineStrs n lo hi).length) := by
  rw [← getElem_nineStrs h, nineNext_getElem]
  by_cases h' : i + 1 < (nineStrs n lo hi).length <;> simp [h']

/-- If the bounds are consistent, there is a string. -/
theorem length_nineStrs_pos (hn : lo ≤ n) (hh : lo ≤ hi) : 0 < (nineStrs n lo hi).length :=
  List.length_pos_iff.mpr fun hnil => by simpa [hnil] using headOpt_nineStrs hn hh

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






/-! ## The leading nines turned into stars -/















/-- A digit other than 9 ends the run. -/
theorem starRunIf_cons_of_ne {d : ℕ} (hd : d ≠ 9) (flag : Bool) (s : List ℕ) :
    starRunIf flag (d :: s) = d :: starRunIf false s := by
  cases flag <;> simp [starRunIf, starRun, hd]

/-- A digit 9 becomes a star while the run goes on, and the run goes on. -/
theorem starRunIf_nine_cons (flag : Bool) (s : List ℕ) :
    starRunIf flag (9 :: s) = (if flag then 10 else 9) :: starRunIf flag s := by
  cases flag <;> simp [starRunIf, starRun]








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






































end

/-! ## The query -/













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




theorem length_starBoxes_eq_length_nineStrs (L m t e : ℕ) :
    (starBoxes L m t e).length = (nineStrs L e (m - t)).length :=
  List.length_map _

/-- Box number i comes from leaf number i. -/
theorem starFirst_mem_starBoxes {L m t e i : ℕ} (hi : i < (nineStrs L e (m - t)).length) :
    starFirst e (nineStrs L e (m - t))[i] ∈ starBoxes L m t e :=
  List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩

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




private theorem cells_set (T : List ℤ) (a : ℕ) (z : ℤ) (ha : a < T.length) :
    cells (T.set a z) = Function.update (cells T) a z := by
  funext x
  by_cases hx : x = a
  · subst hx
    simp [cells, ha]
  · rw [Function.update_of_ne hx]
    simp only [cells, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hx)]

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

/-- The blocks of different vertices are disjoint. -/
private theorem cell_inj (h : TrieInv L lo μ nd fr) {x y : ℕ × List ℕ} {a b : ℕ} (hx : nd x ≠ 0)
    (hy : nd y ≠ 0) (ha : a < 11) (hb : b < 11) (hcell : nd x + b = nd y + a) :
    x = y ∧ b = a := by
  have hrx := h.range x hx
  have hry := h.range y hy
  -- both addresses are lo plus a multiple of 11, and a, b < 11
  exact ⟨h.inj x y hx (by omega), by omega⟩

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

/-- A new vertex for the prefix w ++ [a], at the address fr, with the pointer to it in the vertex
of w. -/
private theorem newChild (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} {a : ℕ} (ha : a < 11)
    (hw : nd (i, w) ≠ 0) (hwa : nd (i, w ++ [a]) = 0) :
    TrieInv L lo (Function.update μ (nd (i, w) + a) fr) (Function.update nd (i, w ++ [a]) fr)
      (fr + 11) := by
  have hin := h.inside hw
  refine h.addVertex hwa (fun j u b happ => ?_) (fun c hc => ?_) fun j u b hu hb hnd => ?_
  · obtain ⟨rfl, happ'⟩ := Prod.mk.inj happ
    rwa [(List.append_inj' happ' rfl).1]
  · rw [Function.update_of_ne (by omega), h.fresh c hc]
  · by_cases hcell : nd (j, u) + b = nd (i, w) + a
    · obtain ⟨hju, rfl⟩ := h.cell_inj hnd hw ha hb hcell
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hju
      rw [Function.update_self, Function.update_self]
    · have hne : (j, u ++ [b]) ≠ (i, w ++ [a]) := fun happ => by
        obtain ⟨rfl, happ'⟩ := Prod.mk.inj happ
        obtain ⟨rfl, hba⟩ := List.append_inj' happ' rfl
        exact hcell (by rw [List.singleton_inj.mp hba])
      rw [Function.update_of_ne hcell, Function.update_of_ne hne, h.child j u b hu hb hnd]

/-- Writing a value into the vertex of a string of full length. -/
private theorem setVal (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (z : ℤ) : TrieInv L lo (Function.update μ (nd (i, w)) z) nd fr := by
  have hin := h.inside hw
  refine { h with child := fun j u b hu hb hnd => ?_, fresh := fun c hc => ?_ }
  · rw [Function.update_of_ne, h.child j u b hu hb hnd]
    intro hcell
    obtain ⟨hju, -⟩ := h.cell_inj (a := 0) hnd hw (by omega) hb hcell
    obtain ⟨-, rfl⟩ := Prod.mk.inj hju
    -- a vertex at depth L is not above depth L
    omega
  · rw [Function.update_of_ne (by omega), h.fresh c hc]

end TrieInv

/-! ## Insertion -/









private theorem TrieExt.trans {L : ℕ} {x : ℕ × List ℕ} {μ μ₁ μ₂ : ℕ → ℤ}
    {nd nd₁ nd₂ : ℕ × List ℕ → ℕ} (h : TrieExt L x μ nd μ₁ nd₁) (h' : TrieExt L x μ₁ nd₁ μ₂ nd₂) :
    TrieExt L x μ nd μ₂ nd₂ := by
  have hne : ∀ y, nd y ≠ 0 → nd₁ y ≠ 0 := fun y hy => by rwa [h.old_vertex y hy]
  refine { old_vertex := fun y hy => ?_, old_root := fun i hi => h.old_root i (h'.old_root i hi),
           old_value := fun i w hL hw hx => ?_ }
  · rw [h'.old_vertex y (hne y hy), h.old_vertex y hy]
  · rw [← h.old_value i w hL hw hx, ← h.old_vertex _ hw, h'.old_value i w hL (hne _ hw) hx]










/-- An insertion after a step that extends the tries. -/
private theorem Inserted.of_step {L lo : ℕ} {x : ℕ × List ℕ} {v : ℤ} {T T₁ T₂ : List ℤ}
    {nd nd₁ nd₂ : ℕ × List ℕ → ℕ} (h : Inserted L lo x v T₁ nd₁ T₂ nd₂)
    (hstep : TrieExt L x (cells T) nd (cells T₁) nd₁) : Inserted L lo x v T nd T₂ nd₂ :=
  { h with ext := hstep.trans h.ext }

section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}

/-- The end of an insertion: the value is written into the vertex of the string. -/
private theorem TrieInv.inserted_set (h : TrieInv L lo (cells T) nd T.length) (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (v : ℤ) : Inserted L lo (i, w) v T nd (T.set (nd (i, w)) v) nd := by
  have hin := h.inside hw
  have hcells : cells (T.set (nd (i, w)) v) = Function.update (cells T) (nd (i, w)) v :=
    cells_set T _ _ (by omega)
  refine { inv := ?_, vertex := hw, value := ?_,
           ext := { old_vertex := fun _ _ => rfl, old_root := fun _ hi => hi,
                    old_value := fun j u _ hu hne => ?_ } }
  · rw [hcells, List.length_set]
    exact h.setVal hL hw v
  · rw [hcells, Function.update_self]
  · rw [hcells, Function.update_of_ne fun hnd => hne (h.inj _ _ hu hnd)]

/-- A step of an insertion where there is no child: a new vertex at the end of the array keeps the
invariant and extends the tries. -/
private theorem TrieInv.step_newChild (h : TrieInv L lo (cells T) nd T.length) {d : ℕ}
    (hd : d < 11) (hw : nd (i, w) ≠ 0) (hlen : w.length < L) (hnone : nd (i, w ++ [d]) = 0)
    (x : ℕ × List ℕ) :
    TrieInv L lo (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length)
        (trieNew (T.set (nd (i, w) + d) T.length)).length ∧
      TrieExt L x (cells T) nd (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length) := by
  have hin := h.inside hw
  rw [cells_trieNew, cells_set T _ _ (by omega), length_trieNew, List.length_set]
  refine ⟨h.newChild hd hw hnone,
    { old_vertex := fun y hy => ?_, old_root := fun j hj => ?_,
      old_value := fun j u hL hu _ => ?_ }⟩
  · exact Function.update_of_ne (fun hyw => hy (by rw [hyw, hnone])) _ _
  · rwa [Function.update_of_ne (by simp)] at hj
  · refine Function.update_of_ne (fun hcell => ?_) _ _
    obtain ⟨hju, -⟩ := h.cell_inj (b := 0) hu hw hd (by omega) hcell
    obtain ⟨-, rfl⟩ := Prod.mk.inj hju
    -- a vertex at depth L is not above depth L
    omega

/-- **Insertion.**  Below the vertex of the prefix w, the insertion of the rest of a string meets
only addresses inside the array, and it achieves what `Inserted` says. -/
private theorem trieInsert_spec (v : ℤ) (key : List ℕ) (hinv : TrieInv L lo (cells T) nd T.length)
    (hw : nd (i, w) ≠ 0) (hlen : w.length + key.length = L) (hkey : ∀ d ∈ key, d < 11) :
    InsertOK T (nd (i, w)) key ∧
      ∃ nd', Inserted L lo (i, w ++ key) v T nd (trieInsert T (nd (i, w)) key v) nd' := by
  induction key generalizing T nd w with
  | nil =>
    rw [List.append_nil]
    exact ⟨hinv.inside hw, nd, hinv.inserted_set hlen hw v⟩
  | cons d l ih =>
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    have hd : d < 11 := hkey d (by simp)
    have hl : ∀ x ∈ l, x < 11 := fun x hx => hkey x (by simp [hx])
    rw [List.length_cons] at hlen
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) := hinv.child i w d (by omega) hd hw
    have hlen' : (w ++ [d]).length + l.length = L := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [List.append_cons, trieInsert, InsertOK, hchild]
    by_cases hz : nd (i, w ++ [d]) = 0
    · -- there is no child: a new vertex at the end of the array
      obtain ⟨hinv₁, hstep⟩ := hinv.step_newChild hd hw (by omega) hz (i, w ++ [d] ++ l)
      obtain ⟨hok, nd', hins⟩ :=
        ih hinv₁ (w := w ++ [d]) (by rw [Function.update_self]; omega) hlen' hl
      rw [Function.update_self] at hok hins
      rw [hz, Int.natCast_zero, if_pos rfl, if_pos rfl]
      exact ⟨⟨hpos, hin, hok⟩, nd', hins.of_step hstep⟩
    · -- the child exists
      obtain ⟨hok, nd', hins⟩ := ih hinv (w := w ++ [d]) hz hlen' hl
      have hz' : (nd (i, w ++ [d]) : ℤ) ≠ 0 := by exact_mod_cast hz
      rw [if_neg hz', if_neg hz', Int.toNat_natCast]
      exact ⟨⟨hpos, hin, by omega, hok⟩, nd', hins⟩

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

/-- What `trieInsert_spec` says about an insertion from the root of trie number i. -/
private theorem insert_spec (nd : ℕ × List ℕ → ℕ) (hinv : TrieInv L lo (cells T) nd T.length)
    (hroots : ∀ i, nd (i, []) = roots i) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
    InsertOK T (roots i) key ∧
      ∃ nd', Inserted L lo (i, key) v T nd (trieInsert T (roots i) key v) nd' := by
  have h := trieInsert_spec (i := i) (w := []) v key hinv (by rwa [hroots]) (by simpa using hk) hd
  rwa [hroots] at h























/-- During an insertion, every cell read holds 0 or the address of a vertex inside the array. -/
theorem insertOK (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) : InsertOK T (roots i) key := by
  obtain ⟨nd, hinv, hroots, -⟩ := h
  exact (insert_spec nd hinv hroots i hi key hk hd 0).1

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









/-- The value of a box without stars is the product at the leaf with its digits. -/
theorem boxValue_zero (encA encB T : List ℤ) (root : ℕ) {l : List ℕ} (hl : ∀ d ∈ l, d < 10) :
    boxValue encA encB T root 0 l = leafProduct encA encB l := by
  rw [boxValue, starsToNines_of_notMem fun h => absurd (hl 10 h) (lt_irrefl 10)]


































private theorem fillTrie_cons (encA encB : List ℤ) (root e : ℕ) (l : List ℕ)
    (boxes : List (List ℕ)) (T : List ℤ) :
    fillTrie encA encB root e (l :: boxes) T
      = fillTrie encA encB root e boxes (trieInsert T root l (boxValue encA encB T root e l)) := rfl

/-- The trie of one more tile is built on top of the tries of the tiles before it. -/
theorem allTries_snoc (L m t : ℕ) (tiles : List TileEnc) (ab : TileEnc) :
    allTries L m t (tiles ++ [ab]) = tileTrie ab.encA ab.encB L m t (allTries L m t tiles) := by
  simp [allTries, List.foldl_append]









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























/-- No tile stands before the first one. -/
theorem tilesBefore_zero : tilesBefore nB encA encB 0 0 = [] := by
  simp [tilesBefore]

/-- The tiles before the next tile of the row are the tiles before the tile, and the tile. -/
theorem tilesBefore_succ (β β' : ℕ) :
    tilesBefore nB encA encB β (β' + 1)
      = tilesBefore nB encA encB β β' ++ [⟨arrT (encA β), arrT (encB β')⟩] := by
  simp [tilesBefore, List.range_succ]

/-- The end of a row is the beginning of the next one. -/
theorem tilesBefore_row (β : ℕ) :
    tilesBefore nB encA encB β nB = tilesBefore nB encA encB (β + 1) 0 := by
  simp [tilesBefore, List.range_succ, List.flatMap_append]

/-- After the last row all tiles have been taken. -/
theorem tilesBefore_all : tilesBefore nB encA encB nB 0 = tileList nB encA encB := by
  simp [tilesBefore, tileList]

/-- β nB + β' tiles stand before the tile (β, β'). -/
theorem length_tilesBefore (β β' : ℕ) :
    (tilesBefore nB encA encB β β').length = β * nB + β' := by
  simp [tilesBefore, List.length_flatMap]

end

/-! ## What the tries of all tiles give to a query

The query for tile number i gets the root of the trie of this tile. -/

section Query

variable {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
  (hi : tiles[i]? = some ab) {η : OutStr L} (hη : (innerSetO η).card = m)

include ht hi hη














end Query












end ThreeSumApsp.Spec

end
end

section


/-!
# Theorem 30 in the light language: procedure numbers, time functions, specifications

This file contains no program, and its only proof is a short remark on the trie area when other
cells change. It states the specifications of the procedures 40 to 53 (`nineFirst` to `queryCore`).
The proof of a routine uses only the specifications of the routines that it calls.

* A routine takes its scalars and the base addresses of its arrays as arguments; no routine but
  `preCore` and `queryAt` knows the memory map. The routines for a tile assume the order in which
  their areas lie (`TileCtx.layout`).
* The specification of a routine is a proposition XSpec lim P: "procedure number Proc.x of the
  program P, started on these arguments in a memory that satisfies this, ends within tX steps with
  this result in a memory that satisfies that". The file of x proves XSpec for every program P that
  holds the body of x at the number Proc.x and meets the specifications of the routines that x
  calls. A caller assumes XSpec and feeds it to the rule for calls. XSpec holds at every depth d of
  calls that leaves the levels which x needs below itself.
* Conventions of the programs: the result of a procedure is what it leaves in its local 0; locals
  that are not arguments start at 0. In the proofs, lines such as "have hw := C.std.space_le" or
  "obtain ⟨⟩ := areas p t b0" state the facts on the limits and on the map that the later steps use.
* The larger routines have two records: XArgs holds the arguments and the data behind them, and
  XPre lim μ x says what the routine assumes about the limits and the memory.
* The pure models are those of the specifications of Section 4 (strings are lists of digits, level 1
  first: P_ij is 3(i - 1) + (j - 1), P₀ is 9, the star is 10).
* Time functions are definitions. The time function of a caller is written in terms of the time
  functions of its callees. Their constants are upper bounds, some with room to spare; only the
  shape matters. The lemmas `within8_tAllTiles` and `exists_tQueryCore_le` compare `tAllTiles` and
  `tQueryCore` with the expressions (8) and L ∑ α_d of the paper.
* Tries use addresses relative to the base tr of the trie area: the cell tr + a of the memory is the
  cell a of the trie array T. The area has cap cells, of which the first T.length are in use;
  nothing is assumed about the others (a new vertex clears its eleven cells); the number T.length
  is kept in the cell fp outside the area.

The routines, the pure functions that model them, and the lemmas that say what the models compute:

| number | routine | model | what is proved about the model |
|---|---|---|---|
| 40 | `nineFirst` | `nineFirst` | `head?_nineStrs`: it is the first string of `nineStrs` |
| 41 | `nineNext` | `nineNext` | `nineNext_getElem`: from string i of `nineStrs` to string i + 1 |
| 42 | `scatter` | `scatter`, `starRunIf` | `lowList` and `boxesOf` are built from them |
| 43 | `starFirst` | `starFirst`, `lastStar` | `starBoxes` is `nineStrs` mapped by `starFirst` |
| 44 | `horner` | `ofDigitList 10` | `ofDigitList_digitsT`: the code of a leaf |
| 45 | `lookup` | `trieLookup` | `TrieRep.lookup`, `TrieRep.walkOK` |
| 46 | `insert` | `trieInsert` | `TrieRep.insert`, `TrieRep.insertOK` |
| 47 | `newRoot` | `trieNew` | `TrieRep.new` |
| 48 | `sumTen` | sum of `tenValues` | `exists_lastStar_of_mem_starBoxes`, `abs_dp_partial_sum_le` |
| 49 | `fillList` | `fillTrie` | `fillTrie_rep`, `length_fillTrie_le` |
| 50 | `tile` | `tileTrie` | `fillUpTo_rep`, `length_tileTrie_le` |
| 51 | `allTiles` | `allTries` | `allTries_rep`, `length_allTries_le`, `lookup_allTries` |
| 52 | `outDigits` | `OutDigitsArgs.digits` | `digitsO_outStrOfPos`: the string of a position |
| 53 | `queryCore` | `trieQuery`, `queryTerms` | `trieQuery_allTries`, `abs_query_partial_sum_le` |

The last line of the table continues with `Theorem30.correct`. The model `boxValue` is computed by a
part of `fillList`, which calls `sumTen` for a box with stars.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## Vocabulary -/









/-- The trie area stays as it is if its cells and the cell fp do not change. -/
theorem TrieMem.keep {μ μ' : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ} (h : TrieMem μ tr cap fp T)
    (hs : SameOn (fun b => Inside tr cap b ∨ b = fp) μ μ' := by ((try refine Light.SameOn.cell ?_);
                                                                      (intro apspMacro_185799_0 apspMacro_185799_1);
                                                                      (first
                                                                        |
                                                                          ((((repeat
                                                                                    (((with_reducible
                                                                                            rename Light.SameOn _ _ _ => apspMacro_185799_2));
                                                                                      ((try
                                                                                            have :=
                                                                                              apspMacro_185799_2 apspMacro_185799_0 (by omega)));
                                                                                      (revert apspMacro_185799_2)));
                                                                                (intros);
                                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                            (omega))
                                                                        |
                                                                          ((simp [] at apspMacro_185799_1);
                                                                            (((repeat
                                                                                    (((with_reducible
                                                                                            rename Light.SameOn _ _ _ => apspMacro_185799_3));
                                                                                      ((try
                                                                                            have :=
                                                                                              apspMacro_185799_3 apspMacro_185799_0 (by omega)));
                                                                                      (revert apspMacro_185799_3)));
                                                                                (intros);
                                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                            (omega))
                                                                        |
                                                                          ((((repeat
                                                                                    (((with_reducible
                                                                                            rename Light.SameOn _ _ _ => apspMacro_185799_4));
                                                                                      ((try
                                                                                            have :=
                                                                                              apspMacro_185799_4 apspMacro_185799_0 (by omega)));
                                                                                      (revert apspMacro_185799_4)));
                                                                                (intros);
                                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                            (fail
                                                                                "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                          its condition K x does not follow from the hypotheses."))))) :
    TrieMem μ' tr cap fp T :=
  have hle := h.le_cap
  ⟨h.seg.keep, (hs fp (.inr rfl)).trans h.free, hle, h.fp_out⟩





/-! ## Procedure numbers

The numbers 0 to 39 belong to Section 2, the numbers from 40 on to Section 4. This file fixes 40 to
53; the files of the other routines of Section 4 fix theirs. -/

namespace Proc















end Proc

/-! ## Time functions -/

































/-! ## The enumeration of the strings with a bounded number of nines -/
















/-! ## Strings -/





























/-! ## Tries -/





















































/-! ## The dynamic program of Lemma 29 -/





































































namespace FillListArgs

variable (x : FillListArgs)















end FillListArgs






















































































































/-! ## A query -/










namespace OutDigitsArgs

variable (x : OutDigitsArgs)











end OutDigitsArgs

























































































end Light.Sec4

end
end

section


/-!
# The tries of all tiles

Proof of Theorem 30, "Preprocessing": "Finally, we compute the values of all the boxes of each of
the at most 4N²/M tiles". The routine `tile` builds the trie of a tile, and this routine calls it
for every tile. The tiles are taken in row-major order. Three pointers move along: the address of
the encoding of the row band, that of the column band, and the cell for the root of the tile. The
text has three parts, one inside the other: one tile (`allTilesStep`), one row of tiles
(`allTilesRow`), all rows (`allTilesBody`). The invariant `AllTiles.Inv` says what the memory holds
before the tile (β, β'); there is one lemma for each part.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace AllTiles






















end AllTiles






























namespace AllTiles

/-! ## The invariant and one tile -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}








































/-- The surroundings of the tile (β, β'). -/
private theorem tileCtx (C : AllTilesPre lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB) :
    TileCtx lim x.L x.m x.t (x.encA β) (x.encB β') (x.aENCA + β * 10 ^ x.L)
      (x.aENCB + β' * 10 ^ x.L) x.tr x.cap x.fp x.cur x.box := by
  have horder := C.order
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  obtain ⟨A, B, hA, hB, hAB⟩ := C.value_le
  generalize β * 10 ^ x.L = a at *
  generalize β' * 10 ^ x.L = b at *
  generalize x.nB * 10 ^ x.L = z at *
  generalize x.nB * x.nB = q at *
  exact
    { std := C.std, ht := C.t_le, hmL := C.m_le, value_le := ⟨A, B, hA β, hB β', hAB⟩
      pow_le := C.pow_le, layout := by ((simp only [Light.InOrder]); (omega)) }

/-- Each tile before (β, β') has one root. -/
private theorem length_roots_triesBefore (x : AllTilesArgs) (β β' : ℕ) :
    (triesBefore x β β').roots.length = β * x.nB + β' := by
  rw [triesBefore, length_roots_allTries, length_tilesBefore]

/-- Before the tile (β, β') the memory holds what tile assumes. -/
private theorem tileArgs_pre (C : AllTilesPre lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB)
    {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') : TilePre lim μ' (tileArgs x β β') := by
  (obtain ⟨⟩ := id C)
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hlenR := length_roots_triesBefore x β β'
  have hlenT := length_allTries_le x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  rw [length_tilesBefore] at hlenT
  have hroom := Nat.mul_add_le_mul hi (le_refl (11 * (1 + x.L * (boxes x.L x.m x.t).card)))
  have hA : Seg μ' (x.aENCA + β * 10 ^ x.L) (arrT (x.encA β)) :=
    (C.segA β hβ).keep (by ((try have := M.same); (try have := length_arrT (x.encA β));
                               (((try refine Light.SameOn.cell ?_);
                                   (intro apspMacro_189880_0 apspMacro_189880_1);
                                   (first
                                     |
                                       ((((repeat
                                                 (((with_reducible
                                                         rename Light.SameOn _ _ _ => apspMacro_189880_2));
                                                   ((try
                                                         have :=
                                                           apspMacro_189880_2 apspMacro_189880_0
                                                             (by omega)));
                                                   (revert apspMacro_189880_2)));
                                             (intros);
                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                         (omega))
                                     |
                                       ((simp [M.same, length_arrT (x.encA β)] at apspMacro_189880_1);
                                         (((repeat
                                                 (((with_reducible
                                                         rename Light.SameOn _ _ _ => apspMacro_189880_3));
                                                   ((try
                                                         have :=
                                                           apspMacro_189880_3 apspMacro_189880_0
                                                             (by omega)));
                                                   (revert apspMacro_189880_3)));
                                             (intros);
                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                         (omega))
                                     |
                                       ((((repeat
                                                 (((with_reducible
                                                         rename Light.SameOn _ _ _ => apspMacro_189880_4));
                                                   ((try
                                                         have :=
                                                           apspMacro_189880_4 apspMacro_189880_0
                                                             (by omega)));
                                                   (revert apspMacro_189880_4)));
                                             (intros);
                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                         (fail
                                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                       its condition K x does not follow from the hypotheses.")))))))
  have hB : Seg μ' (x.aENCB + β' * 10 ^ x.L) (arrT (x.encB β')) :=
    (C.segB β' hβ').keep (by ((try have := M.same); (try have := length_arrT (x.encB β'));
                                 (((try refine Light.SameOn.cell ?_);
                                     (intro apspMacro_190027_0 apspMacro_190027_1);
                                     (first
                                       |
                                         ((((repeat
                                                   (((with_reducible
                                                           rename Light.SameOn _ _ _ => apspMacro_190027_2));
                                                     ((try
                                                           have :=
                                                             apspMacro_190027_2 apspMacro_190027_0
                                                               (by omega)));
                                                     (revert apspMacro_190027_2)));
                                               (intros);
                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                           (omega))
                                       |
                                         ((simp [M.same, length_arrT (x.encB β')] at apspMacro_190027_1);
                                           (((repeat
                                                   (((with_reducible
                                                           rename Light.SameOn _ _ _ => apspMacro_190027_3));
                                                     ((try
                                                           have :=
                                                             apspMacro_190027_3 apspMacro_190027_0
                                                               (by omega)));
                                                     (revert apspMacro_190027_3)));
                                               (intros);
                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                           (omega))
                                       |
                                         ((((repeat
                                                   (((with_reducible
                                                           rename Light.SameOn _ _ _ => apspMacro_190027_4));
                                                     ((try
                                                           have :=
                                                             apspMacro_190027_4 apspMacro_190027_0
                                                               (by omega)));
                                                     (revert apspMacro_190027_4)));
                                               (intros);
                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                           (fail
                                               "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                         its condition K x does not follow from the hypotheses.")))))))
  have hlenT' : (triesBefore x β β').cells.length
      ≤ 1 + (β * x.nB + β') * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) := hlenT
  exact
    { ctx := tileCtx C hβ hβ'
      rep := allTries_rep x.L x.m x.t _
      trie := M.trie
      roots := M.roots
      segA := hA
      segB := hB
      room := by simp only [tileArgs]; omega
      rootsPlace := by simp only [tileArgs, TileArgs.cells]; omega }

/-- The tries after the tile (β, β'). -/
private theorem tries_tileArgs (x : AllTilesArgs) (β β' : ℕ) :
    (tileArgs x β β').tries = triesBefore x β (β' + 1) := by
  rw [triesBefore, tilesBefore_succ, allTries_snoc]
  rfl

/-- The call of `tile` for the tile (β, β') leads from the memory before this tile to the memory
before the next one. -/
private theorem tile_meets (hTile : TileSpec lim P) (C : AllTilesPre lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 3 ≤ lim.depth) {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') :
    Meets lim P Proc.tile d [(x.aENCA + β * 10 ^ x.L : ℕ), (x.aENCB + β' * 10 ^ x.L : ℕ),
      (x.aR + (β * x.nB + β') : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ'
      (tTile x.L x.m x.t) fun _ μ'' => Mem μ μ'' x β (β' + 1) := by
  have horder := C.order
  have hlenR := length_roots_triesBefore x β β'
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hmeets := hTile _ μ' (tileArgs_pre C hβ hβ' M) _ hd
  rw [← hlenR]
  refine hmeets.mono le_rfl fun _ μ'' ⟨htrie, hroots, same⟩ =>
    ⟨tries_tileArgs x β β' ▸ htrie, tries_tileArgs x β β' ▸ hroots,
      M.same.then same fun c hc => ⟨hc, ?_⟩⟩
  -- a cell below cur or behind the trie area is none of those that tile may change
  have hc' : c < x.cur ∨ x.tr + x.cap ≤ c := hc
  simp only [TileArgs.Kept, tileArgs, Outside]
  omega

/-- One tile: the call, and the pointers move on. -/
private theorem step_spec (hTile : TileSpec lim P) (C : AllTilesPre lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 4 ≤ lim.depth) (h : Inv μ x β β' σ) :
    Ends lim P d allTilesStep σ (tTile x.L x.m x.t + 23) (Inv μ x β (β' + 1)) := by
  obtain ⟨void, μ₁, rfl, M⟩ := h
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  -- tile(rowEnc, colEnc, rootPtr, …)
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
            ((tile_meets hTile C hβ hβ' (by omega) M) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (tile_meets hTile C hβ hβ' (by omega) M) ?_ ?_ ?_
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
        ((rintro void' μ₂ M₂);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- rootPtr := rootPtr + 1; colEnc := colEnc + leaves; colBand := colBand + 1
  have hptr : x.aR + (β * x.nB + (β' + 1)) = x.aR + (β * x.nB + β') + 1 := by ring
  have hcol : x.aENCB + (β' + 1) * 10 ^ x.L = x.aENCB + β' * 10 ^ x.L + 10 ^ x.L := by ring
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hcolS := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hbands : x.nB ≤ x.nB * 10 ^ x.L := Nat.le_mul_of_pos_right _ (by positivity)
  unfold Inv
  rw [hptr, hcol]
  -- names for the products
  generalize β * x.nB + β' = ptr at *
  generalize x.aENCA + β * 10 ^ x.L = row at *
  generalize β' * 10 ^ x.L = off at *
  generalize x.nB * 10 ^ x.L = all at *
  generalize 10 ^ x.L = leaves at *
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.aR + ptr + 1 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (x.aENCB + off + leaves : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (β' + 1 : ℕ) ?_ ?_ ?_);
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
  exact ⟨void', μ₂, rfl, M₂⟩

/-! ## One row, and all rows -/

/-- One row of tiles. -/
private theorem row_spec (hTile : TileSpec lim P) (C : AllTilesPre lim μ x) (hβ : β < x.nB)
    (hd : d + 4 ≤ lim.depth) (h : Inv μ x β 0 σ) :
    Ends lim P d allTilesRow σ (x.nB * (tTile x.L x.m x.t + 27) + 16) (Inv μ x (β + 1) 0) := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  -- while β' < nB: one tile
  refine Ends.next _ (Ends.whileConst (Inv μ x β) x.nB (tTile x.L x.m x.t + 23) h ?round ?done
    le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro β' σ hβ' hI
    have hstep := step_spec hTile C hβ hβ' hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by simp, by simpa using hβ', hstep⟩
  case done =>
    rintro _ ⟨void, μ', rfl, M⟩
    refine ⟨by simp, by simp, ?_⟩
    -- rowEnc := rowEnc + leaves; rowBand := rowBand + 1; colBand := 0; colEnc := encB
    have hptr : x.aR + ((β + 1) * x.nB + 0) = x.aR + (β * x.nB + x.nB) := by ring
    have hrow : x.aENCA + (β + 1) * 10 ^ x.L = x.aENCA + β * 10 ^ x.L + 10 ^ x.L := by ring
    have hcol : x.aENCB + 0 * 10 ^ x.L = x.aENCB := by ring
    have hrowS := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
    have hbands : x.nB ≤ x.nB * 10 ^ x.L := Nat.le_mul_of_pos_right _ (by positivity)
    have hbefore : triesBefore x β x.nB = triesBefore x (β + 1) 0 := by
      rw [triesBefore, tilesBefore_row, triesBefore]
    have M' : Mem μ μ' x (β + 1) 0 := ⟨hbefore ▸ M.trie, hbefore ▸ M.roots, M.same⟩
    unfold Inv
    rw [hptr, hrow, hcol]
    -- names for the products
    generalize x.aR + (β * x.nB + x.nB) = ptr at *
    generalize β * 10 ^ x.L = off at *
    generalize x.nB * 10 ^ x.L = all at *
    generalize 10 ^ x.L = leaves at *
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (x.aENCA + off + leaves : ℕ) ?_ ?_ ?_);
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
      (refine Light.Ends.setToThen (β + 1 : ℕ) ?_ ?_ ?_);
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
      (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
      (refine Light.Ends.setToThen (x.aENCB : ℕ) ?_ ?_ ?_);
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
    exact ⟨void, μ', rfl, M'⟩

/-- The time of all rows. -/
private theorem time_le (nB T : ℕ) : 12 + (nB * (4 + (nB * (T + 27) + 16)) + 4)
    ≤ nB * (nB * (T + 80) + 40) + 30 := by
  have hrow : nB * (T + 27) ≤ nB * (T + 80) := Nat.mul_le_mul_left _ (by omega)
  have hall : nB * (4 + (nB * (T + 27) + 16)) ≤ nB * (nB * (T + 80) + 40) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end AllTiles

open AllTiles in
/-- **`allTiles`** meets its specification. -/
theorem allTiles_spec {lim : Limits} {P : Program} (hP : P[Proc.allTiles]? = some allTilesBody)
    (hTile : TileSpec lim P) : AllTilesSpec lim P := by
  intro x μ C
  refine fun d hd => ⟨allTilesBody, hP, ?_⟩
  (obtain ⟨⟩ := id C.std)
  have htime := time_le x.nB (tTile x.L x.m x.t)
  unfold tAllTiles
  -- β := 0; β' := 0; the three pointers at the first tile
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (x.aR : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (x.aENCA : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (x.aENCB : ℕ) ?_ ?_ ?_);
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
            -- while β < nB: one row
            
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
  -- while β < nB: one row
  refine Ends.whileConst (fun β => Inv μ x β 0) x.nB (x.nB * (tTile x.L x.m x.t + 27) + 16) ?start
    ?round ?done (by simp; omega)
  case start =>
    refine ⟨0, μ, by simp, ?_, ?_, .refl⟩
    · rw [triesBefore, tilesBefore_zero]
      exact C.trie
    · rw [triesBefore, tilesBefore_zero]
      simp [allTries, SegN, Seg]
  case round =>
    rintro β σ hβ hI
    have hrow := row_spec hTile C hβ hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by simp, by simpa using hβ, hrow⟩
  case done =>
    rintro _ ⟨void, μ', rfl, M⟩
    have hall : triesBefore x x.nB 0 = x.tries := by
      rw [triesBefore, tilesBefore_all, AllTilesArgs.tries]
    exact ⟨by simp, by simp, hall ▸ M.trie, hall ▸ M.roots, M.same⟩

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

/-- A B ≥ 0 for bounds A, B on the two arrays. -/
theorem mul_nonneg_of_abs_le : 0 ≤ A * B :=
  mul_nonneg ((abs_nonneg _).trans (hA fun _ => Term.P0))
    ((abs_nonneg _).trans (hB fun _ => Term.P0))



























/-- What the dynamic program on digits computes for a cube at depth e is at most 10^e A B in
absolute value. -/
private theorem abs_dpValueD_le (e : ℕ) (π : Cube L) :
    |dpValueD (arrT encA) (arrT encB) e (digitsC π)| ≤ 10 ^ e * (A * B) := by
  rw [dpValueD_digitsC]
  exact abs_dpValue_le hA hB e π

/-- The ten values that the dynamic program adds up for a box with e + 1 stars (the proof of Lemma
29), the star at position ℓ being replaced by the ten terms in the order of their digits: every sum
of an initial part of them is at most 10^{e+1} A B. -/
theorem abs_dp_partial_sum_le (e : ℕ) (π : Cube L) (ℓ : Fin L) (k : ℕ) :
    |((tenValues (dpValueD (arrT encA) (arrT encB) e) (digitsC π) ℓ).take k).sum|
      ≤ 10 ^ (e + 1) * (A * B) := by
  refine (List.abs_sum_take_map_le (List.range 10) _ (B := 10 ^ e * (A * B))
    (fun d hd => ?_) k).trans
    (le_of_eq ?_)
  · -- each of the ten strings is a cube
    have hd' : d < 10 := List.mem_range.mp hd
    have hcube : (digitsC π).set ℓ d = digitsC (Cube.replace π ℓ (termOfIdx ⟨d, hd'⟩)) := by
      rw [digitsC_replace]
      exact congrArg _ (congrArg Fin.val (termEquiv.apply_symm_apply ⟨d, hd'⟩).symm)
    rw [hcube]
    exact abs_dpValueD_le hA hB e _
  · rw [List.length_range]
    push_cast
    ring

/-! ## A query -/




























end ThreeSumApsp.Spec

end
end

section


/-!
# The boxes with e stars go into the trie of their tile (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  "We compute the values of the boxes in
increasing order of their number of stars."  This routine handles the boxes with e stars.  It goes
through the leaves with between e and m - t symbols P₀ in lexicographic order.  For each of them it
turns the first e nines into stars, which gives the next box with e stars; computes the value of the
box, for e = 0 as the product of the two encoded numbers at its code and for e ≥ 1 as the sum of the
values of ten boxes with e - 1 stars, looked up in the trie of the tile; and inserts the box with
its value into the trie.

1. The first section is about lists only: `fillAt` is the trie array after the first i boxes, and
   `StarBox` collects what the routine needs to know about a box with stars (`exists_starBox`).
2. `FillListArgs` holds the data of one run, `FillListPre` what the routine assumes, and
   `FillList.Callees` the specifications of the routines that are called.  `FillList.Inv` is the
   invariant of the loop, and `FillList.RoundFacts` what is known in a round once the box has been
   written.  A round is the call of starFirst, the value (`value_zero_spec`, `value_succ_spec`,
   `fillValue_spec`) and the end of the round (`tail_spec`); together they are `round_spec`, and
   `body_spec` is the whole run.  `fillList_spec` is the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The trie array after the first boxes -/

section pure

variable {L m t : ℕ} {encA encB : Leaf L → ℤ} {e tile lo : ℕ} {roots : ℕ → ℕ}
  {old : ℕ × List ℕ → Option ℤ} {T : List ℤ}





private theorem fillAt_zero (root : ℕ) : fillAt L m t encA encB root e T 0 = T := by
  simp [fillAt, fillTrie]

private theorem fillAt_length (root : ℕ) :
    fillAt L m t encA encB root e T (nineStrs L e (m - t)).length
      = fillTrie (arrT encA) (arrT encB) root e (starBoxes L m t e) T := by
  rw [fillAt, ← length_starBoxes_eq_length_nineStrs, List.take_length]

/-- One more box: it is inserted with the value computed from the array so far. -/
private theorem fillAt_succ (root : ℕ) {i : ℕ} (hi : i < (nineStrs L e (m - t)).length) :
    fillAt L m t encA encB root e T (i + 1)
      = trieInsert (fillAt L m t encA encB root e T i) root
          (starFirst e (nineStrs L e (m - t))[i])
          (boxValue (arrT encA) (arrT encB) (fillAt L m t encA encB root e T i) root e
            (starFirst e (nineStrs L e (m - t))[i])) := by
  have hi' : i < (starBoxes L m t e).length := by rwa [length_starBoxes_eq_length_nineStrs]
  have hbox : (starBoxes L m t e)[i] = starFirst e (nineStrs L e (m - t))[i] := by simp [starBoxes]
  unfold fillAt fillTrie
  rw [← List.take_append_getElem hi', List.foldl_append, hbox]
  rfl

/-- What the tries hold after the first i boxes. -/
private theorem fillAt_rep (hroot : roots tile ≠ 0)
    (hrep : TrieRep L lo T roots (storedUpTo old tile (arrT encA) (arrT encB) L m t e [])) (i : ℕ) :
    TrieRep L lo (fillAt L m t encA encB (roots tile) e T i) roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t e ((starBoxes L m t e).take i)) :=
  fillTrie_rep hroot ((starBoxes L m t e).take i) [] T (fun _ hl => List.mem_of_mem_take hl) hrep

/-- The array grows by at most 11 L cells for each box. -/
private theorem length_fillAt_le (root i : ℕ) :
    (fillAt L m t encA encB root e T i).length ≤ T.length + 11 * L * i :=
  (length_fillTrie_le (arrT encA) (arrT encB) root e L ((starBoxes L m t e).take i)
    (fun _ hl => (starBoxes_digits (List.mem_of_mem_take hl)).1) T).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (List.length_take_le _ _)) _)

/-- An entry of the array of an encoding is a value of the encoding. -/
private theorem abs_getD_arrT_le (enc : Leaf L → ℤ) {A : ℤ} (hA : ∀ τ, |enc τ| ≤ A) {c : ℕ}
    (hc : c < 10 ^ L) : |(arrT enc).getD c 0| ≤ A := by
  have hval : (arrT enc).getD c 0 = enc (decodeT L c) :=
    getD_arrStr_of_lt termEquiv enc hc
  rw [hval]
  exact hA _














/-- A box with e' + 1 stars, in a trie that holds the boxes with at most e' stars, is as `StarBox`
says. -/
private theorem exists_starBox {e' : ℕ} {Ti : List ℤ} {pre : List (List ℕ)} {bx : List ℕ} {A B : ℤ}
    (hA : ∀ τ, |encA τ| ≤ A) (hB : ∀ τ, |encB τ| ≤ B)
    (hrep : TrieRep L lo Ti roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t (e' + 1) pre))
    (hbx : bx ∈ starBoxes L m t (e' + 1)) :
    ∃ p, StarBox L encA encB Ti (roots tile) e' bx (10 ^ (e' + 1) * (A * B)) p := by
  obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hbx
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes bx hbx
  have hpL : p < L := by
    have hstar := ((lastStar_eq_some_iff _ _).1 hp).1
    by_contra hc
    rw [List.getD_eq_default _ _ (by rw [length_digitsC]; omega)] at hstar
    omega
  have hstored : ∀ d < 10, storedUpTo old tile (arrT encA) (arrT encB) L m t (e' + 1) pre
      (tile, (digitsC π).set p d)
        = some (dpValueD (arrT encA) (arrT encB) e' ((digitsC π).set p d)) := fun d hd =>
    storedUpTo_of_lt pre (Nat.lt_succ_self e') (hset d hd)
  have hmap : tenValues (trieLookup Ti (roots tile)) (digitsC π) p
      = tenValues (dpValueD (arrT encA) (arrT encB) e') (digitsC π) p :=
    List.map_congr_left fun d hd => hrep.lookup tile _
      (starBoxes_digits (hset d (List.mem_range.1 hd))).2 _ (hstored d (List.mem_range.1 hd))
  refine ⟨p, hp, hpL, fun d hd => hrep.walkOK tile _ (starBoxes_digits (hset d hd)).2 _
    (hstored d hd), fun j => ?_, by rw [boxValue, sumAtLastStar, hp]⟩
  rw [hmap]
  exact abs_dp_partial_sum_le hA hB e' π ⟨p, hpL⟩ j

end pure

/-! ## The program -/

namespace FillList






















end FillList

open FillList






























namespace FillListArgs

variable (x : FillListArgs)
















end FillListArgs

namespace FillList













































section round

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : FillListArgs} {i : ℕ} {l : List ℕ}
  {Ti : List ℤ} {ν : ℕ → ℤ} {more star value code junk : ℤ}

/-- The end of a round: the box is inserted with its value, and the next leaf is formed. -/
private theorem tail_spec (K : Callees lim P) (H : FillListPre lim μ x) (hd : d + 2 ≤ lim.depth)
    (R : RoundFacts μ x i l Ti ν) :
    Ends lim P d fillTailStmt
      ⟨x.locals more star (x.value Ti (starFirst x.e l)) code junk, ν⟩
      (tInsert x.L + tNineNext x.L + 14) (Inv μ x (i + 1)) := by
  have C := H.ctx
  have hlen := length_of_mem_nineStrs R.leaf_mem
  obtain ⟨hbox_len, hbox_digits⟩ := starBoxes_digits R.box_mem
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  have hlayout := C.layout
  have hsame := R.same
  have hmore : (if (nineNext x.e (x.m - x.t) l).isSome then (1 : ℤ) else 0)
      = if i + 1 < x.leaves.length then 1 else 0 := by
    rw [R.next]
    simp
  -- junk := insert(area, root, box, len, value, free)
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
            ((K.insert
                { tr := x.tr, root := x.root, key := x.box, L := x.L,
                  val := x.value Ti (starFirst x.e l), fp := x.fp, cap := x.cap,
                  T := Ti, kl := starFirst x.e l }
                ν {
                  trie := R.trie, seg := R.box, len := hbox_len,
                  digits := hbox_digits
                  walk := R.rep.insertOK x.tile H.root_ne _ hbox_len hbox_digits
                  room := hbox_len ▸ R.room } _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.insert
              { tr := x.tr, root := x.root, key := x.box, L := x.L,
                val := x.value Ti (starFirst x.e l), fp := x.fp, cap := x.cap,
                T := Ti, kl := starFirst x.e l }
              ν {
                trie := R.trie, seg := R.box, len := hbox_len,
                digits := hbox_digits
                walk := R.rep.insertOK x.tile H.root_ne _ hbox_len hbox_digits
                room := hbox_len ▸ R.room } _ (by omega))
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
        ((rintro _ νins ⟨htrie, hins⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  dsimp only at htrie hins
  -- more := nineNext(leaf, len, stars, m - t)
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
            ((K.next x.cur x.L x.e (x.m - x.t) l νins R.leaf.keep R.leaf_mem
                (by omega) _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.next x.cur x.L x.e (x.m - x.t) l νins R.leaf.keep R.leaf_mem
              (by omega) _ (by omega))
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
        ((rintro res νnext ⟨hnextLeaf, hres, hnext⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hmore] at hres
  rw [R.next] at hnextLeaf
  refine ⟨_, _, _, _, νnext, by rw [hres]; rfl, fun h => ?_, ?_, R.segA.keep, R.segB.keep,
    by ((try refine Light.SameOn.cell ?_);
         (intro apspMacro_207607_0 apspMacro_207607_1);
         (first
           |
             ((((repeat
                       (((with_reducible
                               rename Light.SameOn _ _ _ => apspMacro_207607_2));
                         ((try
                               have :=
                                 apspMacro_207607_2 apspMacro_207607_0 (by omega)));
                         (revert apspMacro_207607_2)));
                   (intros);
                   (try simp only [Function.update_apply, Light.wrote] at *)));
               (omega))
           |
             ((simp [] at apspMacro_207607_1);
               (((repeat
                       (((with_reducible
                               rename Light.SameOn _ _ _ => apspMacro_207607_3));
                         ((try
                               have :=
                                 apspMacro_207607_3 apspMacro_207607_0 (by omega)));
                         (revert apspMacro_207607_3)));
                   (intros);
                   (try simp only [Function.update_apply, Light.wrote] at *)));
               (omega))
           |
             ((((repeat
                       (((with_reducible
                               rename Light.SameOn _ _ _ => apspMacro_207607_4));
                         ((try
                               have :=
                                 apspMacro_207607_4 apspMacro_207607_0 (by omega)));
                         (revert apspMacro_207607_4)));
                   (intros);
                   (try simp only [Function.update_apply, Light.wrote] at *)));
               (fail
                   "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                             SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                             its condition K x does not follow from the hypotheses."))))⟩
  · rwa [List.getElem?_eq_getElem h] at hnextLeaf
  · rw [R.succ]
    exact htrie.keep

/-- The value of a box without stars. -/
private theorem value_zero_spec (K : Callees lim P) (H : FillListPre lim μ x)
    (hd : d + 2 ≤ lim.depth) (he : x.e = 0) (R : RoundFacts μ x i l Ti ν) :
    Ends lim P d fillValueZero ⟨x.locals more star value code junk, ν⟩ (tHorner x.L + 14)
      fun σ' => ∃ code' : ℤ,
        σ' = ⟨x.locals more star (x.value Ti (starFirst x.e l)) code' junk, ν⟩ := by
  have C := H.ctx
  have hw := C.std.space_le
  have hlayout := C.layout
  have hlen := length_of_mem_nineStrs R.leaf_mem
  have hdigits := ((mem_nineStrs l).1 R.leaf_mem).2.1
  obtain ⟨A, B, hA, hB, hword⟩ := C.value_le
  have hbox := R.box
  have hvalue : x.value Ti (starFirst x.e l)
      = (arrT x.encA).getD (ofDigitList 10 l) 0 * (arrT x.encB).getD (ofDigitList 10 l) 0 := by
    rw [FillListArgs.value, he, starFirst_zero, boxValue_zero _ _ Ti x.root hdigits, leafProduct]
  rw [he, starFirst_zero] at hbox
  rw [hvalue]
  have hcode : ofDigitList 10 l < 10 ^ x.L := hlen ▸ ofDigitList_lt l hdigits
  -- code := horner(box, len)
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
            ((K.horner x.box x.L l ν hbox hlen hdigits (by omega) C.pow_le _
                (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.horner x.box x.L l ν hbox hlen hdigits (by omega) C.pow_le _
              (by omega))
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
        ((rintro _ ν' ⟨rfl, hν'⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain rfl : ν = ν' := hν'.symm
  generalize ofDigitList 10 l = c at hcode
  have hcellA : ν (x.aA + c) = (arrT x.encA).getD c 0 := R.segA.getD (by rwa [length_arrT]) 0
  have hcellB : ν (x.aB + c) = (arrT x.encB).getD c 0 := R.segB.getD (by rwa [length_arrT]) 0
  -- the product of two encoded numbers fits in a word
  have hprod : |(arrT x.encA).getD c 0 * (arrT x.encB).getD c 0| ≤ lim.word := by
    have hAc := abs_getD_arrT_le x.encA hA hcode
    rw [abs_mul]
    calc |(arrT x.encA).getD c 0| * |(arrT x.encB).getD c 0|
        ≤ A * B := mul_le_mul hAc (abs_getD_arrT_le x.encB hB hcode) (abs_nonneg _)
          ((abs_nonneg _).trans hAc)
      _ ≤ 10 ^ x.m * (A * B) := le_mul_of_one_le_left
          (mul_nonneg_of_abs_le hA hB) (one_le_pow₀ (by norm_num))
      _ ≤ lim.word := hword
  generalize (arrT x.encA).getD c 0 = y at hcellA hprod
  generalize (arrT x.encB).getD c 0 = z at hcellB hprod
  -- value := mem[encA + code] * mem[encB + code]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (y * z) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcellA,
                hcellB, abs_le.mp hprod]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcellA, hcellB, abs_le.mp hprod] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcellA, hcellB,
                abs_le.mp hprod] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  exact ⟨c, rfl⟩

/-- The value of a box with stars. -/
private theorem value_succ_spec (K : Callees lim P) (H : FillListPre lim μ x)
    (hd : d + 2 ≤ lim.depth) (he : x.e ≠ 0) (R : RoundFacts μ x i l Ti ν) :
    Ends lim P d (.call Proc.sumTen [v Area, v Root, v BoxAt, v Len, v LastStar] Value)
      ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ) value code junk, ν⟩
      (tSumTen x.L + 7) fun σ' =>
        σ' = ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ)
          (x.value Ti (starFirst x.e l)) code junk, ν⟩ := by
  have C := H.ctx
  obtain ⟨hbox_len, hbox_digits⟩ := starBoxes_digits R.box_mem
  obtain ⟨A, B, hA, hB, hword⟩ := C.value_le
  obtain ⟨e', he'⟩ : ∃ e', x.e = e' + 1 := ⟨x.e - 1, by omega⟩
  have hstars := H.stars_le
  have hrep := R.rep
  have hbox_mem := R.box_mem
  have hbox := R.box
  generalize starFirst x.e l = bx at hbox_mem hbox hbox_len hbox_digits ⊢
  dsimp only [FillListArgs.stored] at hrep
  rw [he'] at hrep hbox_mem
  obtain ⟨p, hstar⟩ := exists_starBox hA hB hrep hbox_mem
  have hle := R.trie.le_cap
  have hlayout := C.layout
  -- the partial sums are at most 10^{e'+1} A B ≤ 10^m A B
  have hbound : (10 : ℤ) ^ (e' + 1) * (A * B) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
      (mul_nonneg_of_abs_le hA hB)).trans hword
  have hvalue : x.value Ti bx
      = ((List.range 10).map fun d => trieLookup Ti x.root (bx.set p d)).sum := by
    rw [FillListArgs.value, he']
    exact hstar.value
  rw [hvalue, hstar.last]
  -- value := sumTen(area, root, box, len, lastStar)
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
            ((K.box
                { tr := x.tr, root := x.root, box := x.box, L := x.L, p := p,
                  T := Ti, l := bx }
                ν {
                  area := R.trie.seg, seg := hbox, len := hbox_len,
                  star := hbox_len ▸ hstar.lt
                  digits := hbox_digits, walk := hstar.walk
                  sums := fun j _ => (hstar.sums j).trans hbound } _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.box
              { tr := x.tr, root := x.root, box := x.box, L := x.L, p := p,
                T := Ti, l := bx }
              ν {
                area := R.trie.seg, seg := hbox, len := hbox_len,
                star := hbox_len ▸ hstar.lt
                digits := hbox_digits, walk := hstar.walk
                sums := fun j _ => (hstar.sums j).trans hbound } _ (by omega))
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
        ((rintro _ ν' ⟨rfl, hν'⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hν']
  rfl

/-- The value of the box. -/
private theorem fillValue_spec (K : Callees lim P) (H : FillListPre lim μ x)
    (hd : d + 2 ≤ lim.depth) (R : RoundFacts μ x i l Ti ν) :
    Ends lim P d fillValue
      ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ) value code junk, ν⟩
      (tHorner x.L + tSumTen x.L + 18) fun σ' => ∃ code' : ℤ,
        σ' = ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ)
          (x.value Ti (starFirst x.e l)) code' junk, ν⟩ := by
  have hword := H.ctx.std.const_le
  -- if stars = 0
  refine Ends.iteLast (fun hz => ?_) (fun hz => ?_)
  · focus
       ((refine
             Light.Ends.pieceLast (value_zero_spec K H hd (by simpa using hz) R)
               (fun _ apspMacro_212534_0 => apspMacro_212534_0) ?_);
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
                   | ((ring_nf); (omega)))))
  · exact (value_succ_spec K H hd (by simpa using hz) R).mono (by first
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
                                                                         | ((ring_nf); (omega)))) fun _ h => ⟨code, h⟩

/-- One round of the loop handles leaf number i. -/
private theorem round_spec (K : Callees lim P) (H : FillListPre lim μ x) (hd : d + 2 ≤ lim.depth)
    (hi : i < x.leaves.length) (I : MemInv μ x i ν) :
    Ends lim P d fillRound ⟨x.locals more star value code junk, ν⟩ (tFillRound x.L)
      (Inv μ x (i + 1)) := by
  have C := H.ctx
  have hroom : (x.trieAt i).length + 11 * x.L ≤ x.cap := by
    have hlen : (x.trieAt i).length ≤ x.T.length + 11 * x.L * i :=
      length_fillAt_le x.root i
    have hmul : 11 * x.L * (i + 1) ≤ 11 * x.L * x.leaves.length := Nat.mul_le_mul_left _ hi
    have hcap : x.T.length + 11 * x.L * x.leaves.length ≤ x.cap := by
      have hroom := H.room
      rwa [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs] at hroom
    rw [Nat.mul_add_one] at hmul
    omega
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  have hlayout := C.layout
  have hlen := length_of_mem_nineStrs (List.getElem_mem hi)
  have hsame₀ := I.same
  unfold tFillRound
  -- lastStar := starFirst(leaf, box, len, stars)
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
            ((K.star x.cur x.box x.L x.e _ ν (I.leaf hi) hlen (by omega)
                (by omega) (by omega) _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.star x.cur x.box x.L x.e _ ν (I.leaf hi) hlen (by omega) (by omega)
              (by omega) _ (by omega))
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
        ((rintro _ νbox ⟨hbox, rfl, hsame⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have R : RoundFacts μ x i x.leaves[i] (x.trieAt i) νbox :=
    { leaf_mem := List.getElem_mem hi, box_mem := starFirst_mem_starBoxes hi
      next := nineNext_getElem x.L x.e (x.m - x.t) i hi, succ := fillAt_succ x.root hi
      rep := fillAt_rep H.root_ne H.rep i, room := hroom
      trie := I.trie.keep, segA := I.segA.keep, segB := I.segB.keep, leaf := (I.leaf hi).keep
      box := hbox, same := by ((try refine Light.SameOn.cell ?_);
                                (intro apspMacro_214332_0 apspMacro_214332_1);
                                (first
                                  |
                                    ((((repeat
                                              (((with_reducible
                                                      rename Light.SameOn _ _ _ => apspMacro_214332_2));
                                                ((try
                                                      have :=
                                                        apspMacro_214332_2 apspMacro_214332_0 (by omega)));
                                                (revert apspMacro_214332_2)));
                                          (intros);
                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                      (omega))
                                  |
                                    ((simp [] at apspMacro_214332_1);
                                      (((repeat
                                              (((with_reducible
                                                      rename Light.SameOn _ _ _ => apspMacro_214332_3));
                                                ((try
                                                      have :=
                                                        apspMacro_214332_3 apspMacro_214332_0 (by omega)));
                                                (revert apspMacro_214332_3)));
                                          (intros);
                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                      (omega))
                                  |
                                    ((((repeat
                                              (((with_reducible
                                                      rename Light.SameOn _ _ _ => apspMacro_214332_4));
                                                ((try
                                                      have :=
                                                        apspMacro_214332_4 apspMacro_214332_0 (by omega)));
                                                (revert apspMacro_214332_4)));
                                          (intros);
                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                      (fail
                                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                    its condition K x does not follow from the hypotheses.")))) }
  -- fillValue
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (fillValue_spec K H hd R) ?_ ?_
      | refine Light.Ends.pieceLast (fillValue_spec K H hd R) ?_ ?_);
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
        rintro _
          ⟨code', rfl⟩
              -- fillTailStmt
              )
  -- fillTailStmt
  focus
    ((refine
          Light.Ends.pieceLast (tail_spec K H hd R)
            (fun _ apspMacro_214444_0 => apspMacro_214444_0) ?_);
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
                | ((ring_nf); (omega)))))

/-- The whole run. -/
private theorem body_spec (K : Callees lim P) (H : FillListPre lim μ x)
    (hd : d + 2 ≤ lim.depth) :
    Ends lim P d fillListBody ⟨frame x.vals, μ⟩ (tFillList x.L x.leaves.length) fun σ' =>
        TrieMem σ'.mem x.tr x.cap x.fp (x.trieAt x.leaves.length) ∧
          SameOutsideTile μ σ'.mem x.L x.tr x.cap x.fp x.cur x.box := by
  have C := H.ctx
  have hword := C.std.const_le
  have heL : x.e ≤ x.L := by have := C.ht; have := C.hmL; have := H.stars_le; omega
  have hpos := length_nineStrs_pos heL H.stars_le
  have hfirst : (nineStrs x.L x.e (x.m - x.t))[0] = nineFirst x.L x.e := getElem_nineStrs hpos
  have hlayout := C.layout
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  unfold tFillList
  -- junk := nineFirst(leaf, len, stars)
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
            ((K.first x.cur x.L x.e μ heL (by omega) _ (by omega)) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.first x.cur x.L x.e μ heL (by omega) _ (by omega)) ?_ ?_ ?_ ?_);
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
        ((rintro res ν
              ⟨hleaf, hsame⟩
                  -- more := 1
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- more := 1
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
          (1 : ℕ)
            -- while more = 1
            
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
  -- while more = 1
  refine Ends.whileConst (Inv μ x) x.leaves.length (tFillRound x.L) ?start ?round ?done ?time
  case start =>
    refine ⟨0, 0, 0, res, ν, by rw [if_pos hpos]; rfl, fun _ => hfirst ▸ hleaf, ?_,
      H.segA.keep, H.segB.keep, by ((try refine Light.SameOn.cell ?_);
                                     (intro apspMacro_215676_0 apspMacro_215676_1);
                                     (first
                                       |
                                         ((((repeat
                                                   (((with_reducible
                                                           rename Light.SameOn _ _ _ => apspMacro_215676_2));
                                                     ((try
                                                           have :=
                                                             apspMacro_215676_2 apspMacro_215676_0 (by omega)));
                                                     (revert apspMacro_215676_2)));
                                               (intros);
                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                           (omega))
                                       |
                                         ((simp [] at apspMacro_215676_1);
                                           (((repeat
                                                   (((with_reducible
                                                           rename Light.SameOn _ _ _ => apspMacro_215676_3));
                                                     ((try
                                                           have :=
                                                             apspMacro_215676_3 apspMacro_215676_0 (by omega)));
                                                     (revert apspMacro_215676_3)));
                                               (intros);
                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                           (omega))
                                       |
                                         ((((repeat
                                                   (((with_reducible
                                                           rename Light.SameOn _ _ _ => apspMacro_215676_4));
                                                     ((try
                                                           have :=
                                                             apspMacro_215676_4 apspMacro_215676_0 (by omega)));
                                                     (revert apspMacro_215676_4)));
                                               (intros);
                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                           (fail
                                               "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                         its condition K x does not follow from the hypotheses."))))⟩
    rw [FillListArgs.trieAt, fillAt_zero]
    exact H.trie.keep
  case round =>
    rintro i _ hi ⟨star, value, code, junk, ν', rfl, I⟩
    exact ⟨by simp; omega, by simp [hi], round_spec K H hd hi I⟩
  case done =>
    rintro _ ⟨star, value, code, junk, ν', rfl, I⟩
    exact ⟨by simp; omega, by simp, I.trie, I.same⟩
  case time =>
    -- the test of the loop and a round are the time of one box
    have hstep : ((Light.Cond.eq (v More) (k 1))).cost + 1 + tFillRound x.L = tFillStep x.L := by
      simp [tFillStep]
      omega
    rw [hstep]
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
          | ((ring_nf); (omega)))

end round

end FillList

/-- **fillList** inserts the boxes with e stars, with their values, into the trie of their tile. -/
theorem fillList_spec {lim : Limits} {P : Program} (hP : P[Proc.fillList]? = some fillListBody)
    (hFirst : NineFirstSpec lim P) (hNext : NineNextSpec lim P) (hStar : StarFirstSpec lim P)
    (hHorner : HornerSpec lim P) (hInsert : InsertSpec lim P) (hBox : SumTenSpec lim P) :
    FillListSpec lim P := by
  intro x μ pre d hd
  rw [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs, ← fillAt_length]
  exact .of_body hP (body_spec ⟨hFirst, hNext, hStar, hHorner, hInsert, hBox⟩ pre hd)

end Light.Sec4

end
end

section


/-!
# Horner's rule: the code of a string of decimal digits

horner(a, L) returns the number whose L decimal digits, most significant first, are in the cells
from a.  It is used to index an encoding by a leaf (Section 4.3: "The encodings are indexed by the
leaves (Section 2.4.1) […].  Thus reading the product at a leaf […] takes O(L) operations").

After i rounds the routine holds the number formed by the first i digits (`Horner.Inv`).  One more
digit multiplies it by ten and adds the digit (`ofDigitList_take_succ`), and it stays below 10^L
(`ofDigitList_lt`), which fits in a word.  `horner_spec` is the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

namespace Horner














end Horner











open Horner in
/-- **horner** returns the number with the given decimal digits, and leaves the memory as it
was. -/
theorem horner_spec {lim : Limits} {P : Program} (hP : P[Proc.horner]? = some hornerBody)
    (hs : Std lim) : HornerSpec lim P := by
  rintro a _ l μ hseg rfl hd ha hpow
  refine fun d _ => ⟨hornerBody, hP, ?_⟩
  (obtain ⟨⟩ := id hs)
  -- every number formed on the way is below 10^L, so it fits in a word
  have hfits : ∀ i ≤ l.length, ((ofDigitList 10 (l.take i) : ℕ) : ℤ) < lim.word := fun i hi => by
    have hlt := ofDigitList_lt (b := 10) (l.take i) fun x hx => hd x (List.mem_of_mem_take hx)
    have hpow' : 10 ^ (l.take i).length ≤ 10 ^ l.length :=
      Nat.pow_le_pow_right (by norm_num) (List.length_take_le' _ _)
    exact lt_of_lt_of_le (by exact_mod_cast hlt.trans_le hpow') hpow
  unfold tHorner
  -- level := 0; acc := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (0 : ℕ)
            -- while level < len
            
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
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv a l μ) l.length ?start ?round ?done (hT := le_rfl))
  case start => rfl
  case round =>
    rintro i _ hi rfl
    have hcell : μ (a + i) = (l.getD i 0 : ℕ) := hseg.read hi
    have hnext : ((ofDigitList 10 (l.take (i + 1)) : ℕ) : ℤ)
        = (ofDigitList 10 (l.take i) : ℕ) * 10 + (l.getD i 0 : ℕ) := by
      exact_mod_cast ofDigitList_take_succ 10 l hi
    have hfit := hfits (i + 1) hi
    generalize l.getD i 0 = digit at hcell hnext
    -- acc := acc * 10 + mem[str + level]; level := level + 1
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell] <;> omega)), ?_⟩
    simp [Horner.Inv, update_frame_setLocal, hcell, hnext]
  case done =>
    rintro _ rfl
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- return acc
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (ofDigitList 10 l : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  List.take_length]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [List.take_length] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, List.take_length] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨rfl, rfl⟩

end Light.Sec4

end
end

section


/-!
# Inserting a string into a trie (Lemma 29)

"inserting them into the trie also takes O(L) operations per box, and adds at most L vertices per
box."  New vertices are taken from the end of the part of the trie area that is in use, whose length
is kept in the cell fp.  No routine relies on what the free part of the area holds: the eleven cells
of a new vertex are cleared.  Addresses are relative to the base of the area, so the models are
`Spec.trieNew` and `Spec.trieInsert`.

1. `Ends.clearLoop` is the rule for the loop that clears cells.  `TrieMem.new` and `TrieMem.set`
   say what the trie area holds after a new vertex has been cleared and after a cell has been
   written.
2. `newRoot_spec`: a new vertex as a root.
3. `alloc_spec`: a new vertex as a child.  `Insertion.child` is the array after the test for the
   child, and `Insertion.Progress.step` says that the insertion goes on from the child in that
   array.
4. `insert_spec`: the loop goes down one level in each round (`Insertion.Inv`,
   `Insertion.round_spec`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Clearing cells -/








/-- **The rule for clearLoop.**  The loop clears the n cells from a and changes no local but x. -/
theorem Ends.clearLoop (hs : Std lim) {x y a n T : ℕ} {loc μ : ℕ → ℤ} {Q : State → Prop}
    (hxy : y ≠ x) (hx : loc x = a) (hy : loc y = (a + n : ℕ)) (ha : a + n < lim.space)
    (done : Q ⟨Function.update loc x ((a + n : ℕ) : ℤ), wrote μ a (fun _ => 0) n⟩)
    (hT : n * 11 + 4 ≤ T := by first
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
                                       | ((ring_nf); (omega)))) : Ends lim P d (clearLoop x y) ⟨loc, μ⟩ T Q := by
  (obtain ⟨⟩ := id hs)
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc x ((a + j : ℕ) : ℤ),
    wrote μ a (fun _ => 0) j⟩) n ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hx, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + j).toNat = a + j := by omega
    refine ⟨by simp, by simp [hxy, hy]; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                      ((try have := Light.Std.const_le (by assumption)));
                                                      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    rw [← wrote_succ]
    simp [haddr, add_assoc]
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [hxy, hy], done⟩

/-- The cells that have been cleared. -/
private theorem seg_wrote_zero (μ : ℕ → ℤ) (a n : ℕ) :
    Seg (wrote μ a (fun _ => 0) n) a (List.replicate n 0) := fun i hi => by
  rw [wrote_done (by simpa using hi), List.getElem_replicate]

/-! ## The trie area -/

section

variable {μ μ₁ : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ}

/-- The trie area after a new vertex has been cleared behind the part in use and the free pointer
has been moved. -/
theorem TrieMem.new (h : TrieMem μ tr cap fp T) (hcap : T.length + 11 ≤ cap) :
    TrieMem (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp (trieNew T) ∧
      SameOutsideTrie μ
        (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp := by
  have hfp := h.fp_out
  have hsame : SameOutside μ (wrote μ (tr + T.length) (fun _ => 0) 11) (tr + T.length) 11 :=
    sameOutside_wrote le_rfl
  refine ⟨⟨?_, ?_, ?_, hfp⟩, fun b ⟨hb, hbfp⟩ => ?_⟩
  · refine Seg.update_out (seg_append.2
      ⟨h.seg.keep, seg_wrote_zero _ _ _⟩) ?_ _
    rw [List.length_append, List.length_replicate]
    omega
  · rw [Function.update_self, length_trieNew]
  · rw [length_trieNew]
    exact hcap
  · rw [Function.update_of_ne hbfp]
    exact hsame b (by omega)

/-- Writing into a cell of the part of the trie area that is in use. -/
theorem TrieMem.set (h : TrieMem μ tr cap fp T) {q : ℕ} (hq : q < T.length) (x : ℤ) :
    TrieMem (Function.update μ (tr + q) x) tr cap fp (T.set q x) ∧
      SameOutsideTrie μ (Function.update μ (tr + q) x) tr cap fp := by
  have hfp := h.fp_out
  have hcap := h.le_cap
  refine ⟨⟨h.seg.update_in hq x, ?_, by simpa using hcap, hfp⟩,
    fun b hb => Function.update_of_ne (by omega) _ _⟩
  rw [Function.update_of_ne (by omega), h.free, List.length_set]

end

/-! ## A new root -/

namespace NewRoot











end NewRoot












/-- **newRoot** appends a new vertex to the array, and returns its address. -/
theorem newRoot_spec (hP : P[Proc.newRoot]? = some newRootBody) (hs : Std lim) :
    NewRootSpec lim P := by
  intro tr cap fp T μ hT hcap htr hfp
  refine fun d _ => ⟨newRootBody, hP, ?_⟩
  have hfree := hT.free
  (obtain ⟨⟩ := id hs)
  unfold tNewRoot
  -- new := mem[free]; from := area + new; upto := from + 11
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen T.length ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hfree]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hfree] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hfree] <;> omega)));
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
    (refine Light.Ends.setToThen (tr + T.length : ℕ) ?_ ?_ ?_);
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
          (tr + T.length + 11 : ℕ)
            -- clear the cells of the new vertex
            
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
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
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
        Light.Ends.storeToThen fp
          (T.length + 11 : ℕ)
            -- return new
            
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
  -- return new
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen T.length ?_ ?_ ?_);
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
  exact ⟨rfl, hT.new hcap⟩

/-! ## A new child -/

namespace Insertion

















end Insertion

open Insertion













/-- The new vertex becomes the child in the cell q.  Only the last three locals change. -/
private theorem alloc_spec (hs : Std lim) {tr cap fp q p key L i : ℕ} {val x₈ x₉ x₁₀ : ℤ}
    {T : List ℤ} {μ : ℕ → ℤ} (hT : TrieMem μ tr cap fp T) (hq : q < T.length)
    (hcap : T.length + 11 ≤ cap)
    (htr : tr + cap < lim.space) (hfp : fp < lim.space) :
    Ends lim P d allocStmt ⟨frame [tr, p, key, L, val, fp, i, (tr + q : ℕ), x₈, x₉, x₁₀], μ⟩
      tAlloc
      fun σ' => ∃ (y₈ y₉ y₁₀ : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame [tr, p, key, L, val, fp, i, (tr + q : ℕ), y₈, y₉, y₁₀], μ'⟩ ∧
          TrieMem μ' tr cap fp (trieNew (T.set q T.length)) ∧ SameOutsideTrie μ μ' tr cap fp := by
  have hfree := hT.free
  (obtain ⟨⟩ := id hs)
  obtain ⟨hset, hsame⟩ := hT.set hq (T.length : ℤ)
  have hnew := hset.new (by rw [List.length_set]; exact hcap)
  rw [List.length_set] at hnew
  unfold tAlloc
  -- new := mem[free]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen T.length ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hfree]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hfree] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hfree] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- mem[cell] := new
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (tr + q) T.length ?_ ?_ ?_);
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
  -- from := area + new; upto := from + 11
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (tr + T.length : ℕ) ?_ ?_ ?_);
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
          (tr + T.length + 11 : ℕ)
            -- clear the cells of the new vertex
            
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
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen fp (T.length + 11 : ℕ) ?_ ?_ ?_);
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
  exact ⟨_, _, _, _, rfl, hnew.1, hsame.trans hnew.2⟩

/-! ## Insertion -/














namespace Insertion

/-- The pointer to a new child, read back from the array. -/
private theorem getD_trieNew_set {T : List ℤ} {q : ℕ} (hq : q < T.length) (x : ℤ) :
    (trieNew (T.set q x)).getD q 0 = x := by
  rw [trieNew, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hq),
    List.getElem?_set_self hq]
  rfl















section

variable {T Ti : List ℤ} {root i p : ℕ} {kl : List ℕ} {val : ℤ}

/-- The current vertex lies inside the array. -/
theorem Progress.inside (h : Progress T root kl val i Ti p) : p + 11 ≤ Ti.length := by
  have hok := h.ok
  generalize kl.drop i = rest at hok
  cases rest with
  | nil => exact hok.2
  | cons x rest => exact hok.2.1

/-- One level down: in the array with the child, the pointer to the child is positive, and the
insertion goes on from the child. -/
theorem Progress.step (h : Progress T root kl val i Ti p) (hi : i < kl.length)
    (hsym : kl[i] < 11) :
    0 < (child Ti (p + kl[i])).getD (p + kl[i]) 0 ∧
      Progress T root kl val (i + 1) (child Ti (p + kl[i]))
        ((child Ti (p + kl[i])).getD (p + kl[i]) 0).toNat := by
  have hin := h.inside
  have hlen := h.len
  have hok := h.ok
  have heq := h.eq
  rw [List.drop_eq_getElem_cons hi] at hok heq
  rw [trieInsert] at heq
  obtain ⟨hpos, -, hbranch⟩ := hok
  unfold child
  by_cases hz : Ti.getD (p + kl[i]) 0 = 0
  · -- there is no child: a new vertex at the end of the array
    rw [if_pos hz] at hbranch heq ⊢
    rw [getD_trieNew_set (by omega), Int.toNat_natCast]
    exact ⟨by omega, hbranch, heq, by rw [length_trieNew, List.length_set]; omega⟩
  · -- the child exists
    rw [if_neg hz] at hbranch heq ⊢
    exact ⟨hbranch.1, hbranch.2, heq, by omega⟩

end









section

variable {x : InsertArgs} {i p q : ℕ} {x₇ x₈ x₉ x₁₀ : ℤ} {Ti : List ℤ} {μ μ' : ℕ → ℤ}




/-- The end of a round, once the area holds the array with the child: vertex := mem[cell].  The
conclusion has the form that the rule for counting loops asks for: the loop itself then raises the
level. -/
private theorem down_spec (C : InsertPre lim μ x) {t : ℕ} (ht : 3 ≤ t)
    (hq : q < Ti.length) (hchild : 0 < (child Ti q).getD q 0)
    (hnext : Progress x.T x.root x.kl x.val (i + 1) (child Ti q) ((child Ti q).getD q 0).toNat)
    (hmem : TrieMem μ' x.tr x.cap x.fp (child Ti q))
    (hsame : SameOutsideTrie μ μ' x.tr x.cap x.fp) :
    Ends lim P d (.set Vertex (M (v Cell)))
      ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, (x.tr + q : ℕ), x₈, x₉, x₁₀], μ'⟩ t
      fun σ' => σ'.loc Level = i ∧ Inv x μ (i + 1)
        { σ' with loc := Function.update σ'.loc Level ((i : ℤ) + 1) } := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id hmem))
  have hq' : q < (child Ti q).length := by
    unfold child
    split_ifs
    · rw [length_trieNew, List.length_set]
      omega
    · exact hq
  have hread := hmem.seg.getD hq' 0
  generalize (child Ti q).getD q 0 = c at hchild hnext hread
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (c.toNat : ℕ) ?_ ?_ ?_);
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
  exact ⟨rfl, _, _, _, _, _, _, _, by rw [update_frame_setLocal]; rfl, hnext, hmem, hsame⟩

/-- One round goes down one level, with a new child if there was none. -/
private theorem round_spec (hs : Std lim) (C : InsertPre lim μ x) (hi : i < x.kl.length)
    (hprog : Progress x.T x.root x.kl x.val i Ti p) (hmem : TrieMem μ' x.tr x.cap x.fp Ti)
    (hsame : SameOutsideTrie μ μ' x.tr x.cap x.fp) :
    Ends lim P d insertRound
      ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, x₇, x₈, x₉, x₁₀], μ'⟩ tRound
      fun σ' => σ'.loc Level = i ∧ Inv x μ (i + 1)
        { σ' with loc := Function.update σ'.loc Level ((i : ℤ) + 1) } := by
  have hroom := C.room
  have harea := C.area_in
  have hin := hprog.inside
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id hmem); (obtain ⟨⟩ := id hprog);
    (obtain ⟨⟩ := id hs))
  have hsym : x.kl[i] < 11 := C.digits _ (List.getElem_mem hi)
  obtain ⟨hchild, hnext⟩ := hprog.step hi hsym
  have hcell : μ' (x.key + i) = (x.kl[i] : ℕ) :=
    (hsame _ ⟨by omega, by omega⟩).trans (C.seg.getElem hi)
  have hq : p + x.kl[i] < Ti.length := by omega
  unfold tRound
  -- cell := area + vertex + mem[key + level]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.tr + (p + x.kl[i]) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcell]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcell] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  generalize p + x.kl[i] = q at hchild hnext hq ⊢
  have hptr : μ' (x.tr + q) = Ti.getD q 0 := hmem.seg.getD hq 0
  -- if mem[cell] = 0
  refine Ends.iteThen (fun hz => ?_) (fun hz => ?_) (by (((try have := Light.Std.space_le (by assumption)));
                                                          ((try have := Light.Std.const_le (by assumption)));
                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
  · -- there is no child: a new vertex
    have hz' : Ti.getD q 0 = 0 := by
      rw [← hptr]
      simpa using hz
    refine Ends.next _ ((alloc_spec hs hmem hq (by omega) harea C.free_in).mono le_rfl ?_)
    rintro _ ⟨y₈, y₉, y₁₀, μ₂, rfl, hmem₂, hsame₂⟩
    exact down_spec C (by first
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
                                | ((ring_nf); (omega)))) hq hchild hnext (by rw [child, if_pos hz']; exact hmem₂)
      (hsame.trans hsame₂)
  · -- the child exists
    have hz' : Ti.getD q 0 ≠ 0 := by
      rw [← hptr]
      simpa using hz
    refine Ends.next 0 (Ends.skip ?_)
    exact down_spec C (by first
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
                                | ((ring_nf); (omega)))) hq hchild hnext (by rw [child, if_neg hz']; exact hmem)
      hsame

end

end Insertion

/-- **insert** stores the value for the string: the area then holds `Spec.trieInsert`. -/
theorem insert_spec (hP : P[Proc.insert]? = some insertBody) (hs : Std lim) :
    InsertSpec lim P := by
  intro x μ pre d _
  refine .of_body hP ?_
  rw [InsertArgs.vals, ← pre.len]
  ((obtain ⟨⟩ := id hs); (obtain ⟨⟩ := id pre))
  unfold tInsert
  -- for level < len
  refine Ends.next _ (Ends.for (Inv x μ) x.kl.length tRound ?start ?round
    ?done ?bound (hT := le_rfl)) (by simp [tRound, tAlloc]; omega)
  case start =>
    exact ⟨x.T, x.root, 0, 0, 0, 0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 4]; rfl,
      ⟨pre.walk, rfl, by omega⟩, pre.trie, .refl⟩
  case bound =>
    rintro i _ - - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, hprog, hmem, hsame⟩
    exact round_spec hs pre hi hprog hmem hsame
  case done =>
    rintro _ - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, hprog, hmem, hsame⟩
    have hin := hprog.inside
    have hle := hmem.le_cap
    obtain ⟨hset, hsame'⟩ := hmem.set (q := p) (by omega) x.val
    have heq := hprog.eq
    rw [List.drop_length, trieInsert] at heq
    simp only [tRound, tAlloc]
    -- mem[area + vertex] := value
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (x.tr + p) x.val ?_ ?_ ?_);
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
    exact ⟨heq ▸ hset, hsame.trans hsame'⟩

end Light.Sec4

end
end

section


/-!
# Looking up a string in a trie (Section 4.3)

"looking up or inserting a box, takes O(L) operations": the routine follows the symbols of the box
down from the root.  A vertex is a block of eleven consecutive cells of the trie area, one for each
symbol, holding the address of the child; a vertex at depth L holds the value in its first cell.
Addresses are relative to the base of the area, so the model is `Spec.trieLookup` on the array T
that the area holds.

The loop goes down one level in each round.  Its invariant (`Lookup.Inv`) says that the walk from
the current vertex along the rest of the string ends where the walk from the root along the whole
string ends, and that it stays inside the array (`Spec.WalkOK`); `Lookup.walk_step` says what one
step down does to both facts.  `lookup_spec` is the specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Lookup











end Lookup











namespace Lookup

variable {T : List ℤ} {kl : List ℕ} {p i : ℕ}

/-- One step down: the current vertex lies inside the array, the pointer for the next symbol is
positive, and the walk goes on from the child. -/
private theorem walk_step (hi : i < kl.length) (hok : WalkOK T p (kl.drop i)) :
    p + 11 ≤ T.length ∧ 0 < T.getD (p + kl[i]) 0 ∧
      WalkOK T (T.getD (p + kl[i]) 0).toNat (kl.drop (i + 1)) ∧
      trieWalk T p (kl.drop i) = trieWalk T (T.getD (p + kl[i]) 0).toNat (kl.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi] at hok ⊢
  exact ⟨hok.2.1, hok.2.2.1, hok.2.2.2, rfl⟩







end Lookup

open Lookup in
/-- **lookup** returns the value stored for the string, and leaves the memory as it was. -/
theorem lookup_spec {lim : Limits} {P : Program} (hP : P[Proc.lookup]? = some lookupBody)
    (hs : Std lim) : LookupSpec lim P := by
  rintro tr root key _ T kl μ hT hkey rfl hd hwalk htr hkeyB
  refine fun d _ => ⟨lookupBody, hP, ?_⟩
  (obtain ⟨⟩ := id hs)
  unfold tLookup
  -- level := 0
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
          (0 : ℕ)
            -- while level < len
            
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
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv tr root key T kl μ) kl.length ?start ?round ?done
    (hT := le_rfl))
  case start => exact ⟨root, rfl, hwalk, rfl⟩
  case round =>
    rintro i _ hi ⟨p, rfl, hok, hwk⟩
    obtain ⟨hpT, hpos, hok', hstep⟩ := walk_step hi hok
    have hsym : kl[i] < 11 := hd _ (List.getElem_mem hi)
    have hcell : μ (key + i) = (kl[i] : ℕ) := hkey.getElem hi
    have hnext : μ (tr + (p + kl[i])) = T.getD (p + kl[i]) 0 := hT.getD (by omega) 0
    have haddr : ((tr : ℤ) + p + (kl[i] : ℕ)).toNat = tr + (p + kl[i]) := by omega
    -- vertex := mem[area + vertex + mem[key + level]]; level := level + 1
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell] <;> omega)),
      (T.getD (p + kl[i]) 0).toNat, ?_, hok', hwk.trans hstep⟩
    rw [Int.toNat_of_nonneg hpos.le]
    simp [update_frame_setLocal, hcell, haddr, hnext]
  case done =>
    rintro _ ⟨p, rfl, hok, hwk⟩
    rw [List.drop_of_length_le le_rfl] at hok hwk
    have hin := hok.2
    have hread : μ (tr + p) = T.getD p 0 := hT.getD (by omega) 0
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- return mem[area + vertex]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (T.getD p 0) ?_ ?_ ?_);
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
    refine ⟨?_, rfl⟩
    rw [trieLookup, hwk]
    rfl

end Light.Sec4

end
end

section


/-!
# The least string with a given number of nines

nineFirst(a, n, lo) writes n - lo zeros and then lo nines into the cells from a: the first string of
the enumeration `Spec.nineStrs n lo hi`.  The two loops that write zeros and then nines up to the
end of the string are also the end of nineNext, so they are a statement of their own, `fillTail`.

Each of the two loops writes one digit again and again while a test holds (`fillRun`,
`Ends.fillRun`).  Together they write the least string from the current position on
(`fillTail_spec`), and `nineFirst_spec` is the case of the position 0.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine











end Nine

open Nine

/-! ## One digit again and again -/







/-- The cells that have been written hold the digit. -/
private theorem segN_wrote_const (μ : ℕ → ℤ) (dst c n : ℕ) :
    SegN (wrote μ dst (fun _ => (c : ℤ)) n) dst (List.replicate n c) := fun i hi => by
  rw [wrote_done (by simpa using hi)]
  simp

/-- **The rule for fillRun.**  The test is safe and holds in the first cnt rounds and no longer; it
may depend on the position, not on the memory.  Then the digit c is written into cnt cells.  (A
constant up to 100 fits in a word.) -/
theorem Ends.fillRun (hs : Std lim) {test : Cond} {c a i₀ cnt T : ℕ} {loc μ : ℕ → ℤ}
    {Q : State → Prop} (hc : c ≤ 100) (ha : a + (i₀ + cnt) < lim.space) (hstr : loc Str = a)
    (hpos : loc Pos = i₀)
    (htest : ∀ j ≤ cnt, ∀ μ', test.Safe lim ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ), μ'⟩ ∧
      (test.Holds ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ), μ'⟩ ↔ j < cnt))
    (done : Q ⟨Function.update loc Pos ((i₀ + cnt : ℕ) : ℤ),
      wrote μ (a + i₀) (fun _ => (c : ℤ)) cnt⟩)
    (hT : cnt * (test.cost + 1 + 9) + (test.cost + 1) ≤ T := by first
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
    Ends lim P d (fillRun test c) ⟨loc, μ⟩ T Q := by
  (obtain ⟨⟩ := id hs)
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ),
    wrote μ (a + i₀) (fun _ => (c : ℤ)) j⟩) cnt ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hpos, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + ((i₀ : ℤ) + j)).toNat = a + i₀ + j := by omega
    refine ⟨(htest j hj.le _).1, (htest j hj.le _).2.mpr hj,
      by (((try have := Light.Std.space_le (by assumption)));
           ((try have := Light.Std.const_le (by assumption)));
           (simp [Light.Limits.Addr, abs_le, -abs_mul, hstr] <;> omega)), ?_⟩
    rw [← wrote_succ]
    simp [hstr, haddr, add_assoc]
  case done =>
    rintro _ rfl
    exact ⟨(htest cnt le_rfl _).1, fun h => absurd ((htest cnt le_rfl _).2.mp h) (lt_irrefl _),
      done⟩

/-! ## Zeros and then nines up to the end of the string -/







/-- fillTail writes the least string with need nines into the cells from the position i₀ on. -/
theorem fillTail_spec (hs : Std lim) {μ : ℕ → ℤ} {a n i₀ need : ℕ} (ha : a + n < lim.space)
    (hfit : i₀ + need ≤ n) (loc : ℕ → ℤ) (hstr : loc Str = a) (hlen : loc Len = n)
    (hpos : loc Pos = i₀) (hneed : loc _root_.Light.Sec4.Nine.Need = need) :
    Ends lim P d fillTail ⟨loc, μ⟩ (15 * (n - i₀) + 10) fun σ' =>
      σ'.loc = Function.update loc Pos n ∧ SegN σ'.mem (a + i₀) (nineFirst (n - i₀) need) ∧
        SameOutside μ σ'.mem (a + i₀) (n - i₀) := by
  have hw := hs.space_le
  have hmid : i₀ + (n - i₀ - need) = n - need := by omega
  -- zeros while pos + need < len
  refine Ends.next _ (Ends.fillRun hs (a := a) (i₀ := i₀) (cnt := n - i₀ - need) (by norm_num)
    (by omega) hstr hpos
    (fun j hj μ' => by (((try have := Light.Std.space_le (by assumption)));
                          ((try have := Light.Std.const_le (by assumption)));
                          (simp [Light.Limits.Addr, abs_le, -abs_mul, hlen, hneed] <;> omega))) ?_ (hT := le_rfl)) (by simp; omega)
  -- nines while pos < len
  refine Ends.fillRun hs (a := a) (i₀ := n - need) (cnt := need) (by norm_num) (by omega)
    (by simpa using hstr) (by simp [hmid]) (fun j hj μ' => by simp [hlen]; omega) ?_
    (by simp; omega)
  -- the zeros are kept by the second loop, and both loops stay within the n - i₀ cells
  have hzeros := segN_wrote_const μ (a + i₀) 0 (n - i₀ - need)
  have hsame₀ : SameOutside μ (wrote μ (a + i₀) (fun _ => ((0 : ℕ) : ℤ)) (n - i₀ - need)) (a + i₀)
      (n - i₀ - need) := sameOutside_wrote le_rfl
  generalize wrote μ (a + i₀) (fun _ => ((0 : ℕ) : ℤ)) (n - i₀ - need) = μ₀ at hzeros hsame₀ ⊢
  have hsame₉ : SameOutside μ₀ (wrote μ₀ (a + (n - need)) (fun _ => ((9 : ℕ) : ℤ)) need)
      (a + (n - need)) need := sameOutside_wrote le_rfl
  refine ⟨by simp [Nat.sub_add_cancel (show need ≤ n by omega)], ?_,
    (hsame₀.mono le_rfl (by omega)).trans (hsame₉.mono (by omega) (by omega))⟩
  have hdst : a + i₀ + (List.map (fun x : ℕ => (x : ℤ)) (List.replicate (n - i₀ - need) 0)).length
      = a + (n - need) := by simp; omega
  rw [nineFirst, SegN, List.map_append, seg_append, hdst]
  exact ⟨hzeros.keep, segN_wrote_const _ _ 9 _⟩

/-! ## The least string -/







/-- **nineFirst** writes the least string of n digits with lo nines. -/
theorem nineFirst_spec (hP : P[Proc.nineFirst]? = some nineFirstBody) (hs : Std lim) :
    NineFirstSpec lim P := by
  intro a n lo μ hlo ha
  refine fun d _ => ⟨nineFirstBody, hP, ?_⟩
  have hword := hs.const_le
  unfold tNineFirst
  -- pos := 0; need := minNines
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen lo ?_ ?_ ?_);
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
  -- fillTail
  refine (fillTail_spec hs (i₀ := 0) (need := lo) ha (by omega) _ rfl rfl rfl rfl).mono
    (by simp; omega) ?_
  rintro σ' ⟨-, hseg, hsame⟩
  exact ⟨hseg, hsame⟩

end Light.Sec4

end
end

section


/-!
# The successor of a string, as two passes from left to right

`nineNext`, which goes from a string with a bounded number of nines to the next one, is defined by
recursion on the string.  A machine goes through the cells of a buffer from left to right.  This
file gives the function in that shape.

* One pass over the string finds the last position whose digit can be raised, and the number of
  nines before it (`nineScan`).
* A second pass writes the next string: the digits before that position are kept, its digit is
  raised by one, and the rest is filled with zeros followed by nines (`raiseAt`).

The result is `nineNext_eq_scan`.  It is proved in two steps: `nineNext` raises the last position
that can be raised (`raisePos`, `nineNext_eq_raise`), and the scan finds that position
(`nineScanFrom_eq`).  For the routine there are, besides, an invariant of the scan
(`nineScan_inv`) and the fact that the filling fits behind the position that is raised
(`raise_fits`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The last position that can be raised -/




















/-- A digit that can be raised is at most 8. -/
theorem le_of_canRaise {hi c d : ℕ} (h : canRaise hi c d = true) : d ≤ 8 := by
  simp only [canRaise, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  omega

/-- What `nineNext` does to the first digit when the rest of the string cannot be raised. -/
private theorem raise_head (lo hi c d : ℕ) (l : List ℕ) :
    nineRaise (lo - c) (hi - c) l.length d
      = (if canRaise hi c d then some (0, c) else none).map
          fun q : ℕ × ℕ => raiseAt lo q.1 q.2 (d :: l) := by
  rw [nineRaise]
  by_cases h8 : d < 8
  · simp [canRaise, h8, raiseAt, Nat.ne_of_lt h8]
  · by_cases h : d = 8 ∧ c < hi
    · simp [canRaise, h.1, h.2, raiseAt]
    · have hcan : canRaise hi c d = false := by
        simp only [canRaise, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
        exact ⟨h8, by tauto⟩
      rw [if_neg h8, if_neg fun h' => h ⟨h'.1, by omega⟩, hcan]
      rfl

/-- `nineNext` raises the last position that can be raised. -/
private theorem nineNext_eq_raise (lo hi c : ℕ) (l : List ℕ) :
    nineNext (lo - c) (hi - c) l = (raisePos hi c l).map fun q => raiseAt lo q.1 q.2 l := by
  induction l generalizing c with
  | nil => rfl
  | cons d l ih =>
    have hlo : (if d = 9 then lo - c - 1 else lo - c) = lo - (if d = 9 then c + 1 else c) := by
      split_ifs <;> omega
    have hhi : (if d = 9 then hi - c - 1 else hi - c) = hi - (if d = 9 then c + 1 else c) := by
      split_ifs <;> omega
    rw [nineNext, raisePos, hlo, hhi, ih]
    rcases raisePos hi (if d = 9 then c + 1 else c) l with _ | ⟨p, c'⟩
    · exact raise_head lo hi c d l
    · simp [raiseAt]

/-! ## The scan from left to right -/
























/-- The scan of two lists one after the other: the second list is scanned from the state after the
first. -/
private theorem nineScanFrom_append (hi i : ℕ) (l l' : List ℕ) (s : NineScan) :
    nineScanFrom hi i (l ++ l') s = nineScanFrom hi (i + l.length) l' (nineScanFrom hi i l s) := by
  induction l generalizing i s with
  | nil => rfl
  | cons d l ih =>
    rw [List.cons_append, nineScanFrom, nineScanFrom, ih, List.length_cons]
    congr 1
    omega

/-- The state after one more cell is one step of the scan from the state before that cell. -/
theorem nineScan_succ (hi : ℕ) (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    nineScan hi l (j + 1) = nineScanStep hi j (l.getD j 0) (nineScan hi l j) := by
  rw [nineScan, nineScan, List.take_succ_getD l hj 0, nineScanFrom_append, List.length_take,
    Nat.min_eq_left hj.le, Nat.zero_add]
  rfl

/-- The scan finds the last position that can be raised. -/
private theorem nineScanFrom_eq (hi i : ℕ) (l : List ℕ) (s : NineScan) :
    nineScanFrom hi i l s =
      match raisePos hi s.nines l with
      | some (p, c) => ⟨1, i + p, c, s.nines + l.count 9⟩
      | none => ⟨s.found, s.pos, s.before, s.nines + l.count 9⟩ := by
  induction l generalizing i s with
  | nil => rfl
  | cons d l ih =>
    have hn : (nineScanStep hi i d s).nines = if d = 9 then s.nines + 1 else s.nines := rfl
    have hcount : (if d = 9 then s.nines + 1 else s.nines) + l.count 9
        = s.nines + (d :: l).count 9 := by
      by_cases h : d = 9
      · rw [h, if_pos rfl, List.count_cons_self]
        omega
      · rw [if_neg h, List.count_cons_of_ne h]
    rw [nineScanFrom, ih, raisePos, hn, hcount]
    rcases raisePos hi (if d = 9 then s.nines + 1 else s.nines) l with _ | ⟨p, c⟩
    · by_cases hc : canRaise hi s.nines d <;> simp [nineScanStep, hc]
    · simp only [NineScan.mk.injEq, true_and, and_true]
      omega

/-- **The successor by two passes.**  After the scan of the whole string, either no position can be
raised and the string is the last one, or the next string is obtained by raising the position
found. -/
theorem nineNext_eq_scan (lo hi : ℕ) (l : List ℕ) :
    nineNext lo hi l =
      if (nineScan hi l l.length).found = 1 then
        some (raiseAt lo (nineScan hi l l.length).pos (nineScan hi l l.length).before l)
      else none := by
  have h := nineNext_eq_raise lo hi 0 l
  rw [Nat.sub_zero, Nat.sub_zero] at h
  rw [h, nineScan, List.take_length, nineScanFrom_eq]
  rcases raisePos hi 0 l with _ | ⟨p, c⟩ <;> simp

/-! ## What the scan has found -/











theorem nineScan_inv (hi : ℕ) (l : List ℕ) {j : ℕ} (hj : j ≤ l.length) :
    NineScanInv hi l j (nineScan hi l j) := by
  induction j with
  | zero => exact ⟨rfl, Or.inl rfl, nofun, nofun, nofun⟩
  | succ j ih =>
    have ih := ih (Nat.le_of_succ_le hj)
    rw [nineScan_succ hi l hj]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [nineScanStep]
    · rw [List.count_take_succ_getD l 9 hj 0, ← ih.nines]
      split_ifs <;> rfl
    · split_ifs
      · exact Or.inr rfl
      · exact ih.found
    · split_ifs
      · exact fun _ => Nat.lt_succ_self j
      · exact fun hf => (ih.pos_lt hf).trans (Nat.lt_succ_self j)
    · split_ifs with hc
      · exact fun _ => hc
      · exact ih.canRaise
    · split_ifs
      · exact fun _ => ih.nines
      · exact ih.before

/-! ## The filling fits -/

/-- Behind a position that can be raised there is room for the nines that are still needed. -/
theorem raise_fits {lo p : ℕ} {l : List ℕ} (hp : p < l.length) (h8 : l.getD p 0 ≤ 8)
    (hlo : lo ≤ l.count 9) : lo - (l.take p).count 9 ≤ l.length - p - 1 := by
  have hsplit : l.count 9 = (l.take p).count 9 + (l.drop p).count 9 := by
    rw [← List.count_append, List.take_append_drop]
  have hdrop : (l.drop p).count 9 = (l.drop (p + 1)).count 9 := by
    rw [List.drop_eq_getElem_cons hp, List.count_cons_of_ne]
    rw [List.getD_eq_getElem _ _ hp] at h8
    omega
  have hle := List.count_le_length (a := 9) (l := l.drop (p + 1))
  rw [List.length_drop] at hle
  omega

end ThreeSumApsp.Spec

end
end

section


/-!
# The next string of the enumeration

nineNext(a, n, lo, hi) replaces the string of n digits at a by the next string with between lo and
hi nines (`Spec.nineNext`), and returns 1; if the string is the last one, it leaves it and
returns 0.  This is the step of all three enumerations of Section 4 (proof of Lemma 29: "Generating
the boxes with e stars […] also takes O(L) operations per box"; proof of Theorem 30: "Enumerating
them also takes O(L) operations per number").

There are two passes, as in `Spec.nineNext_eq_scan`.
1. The first pass finds the last position that can be raised and the number of nines before it.  One
   round is `Spec.nineScanStep` (`scanRound_runs`), so after i rounds the locals hold
   `Spec.nineScan hi l i` (`ScanInv`).
2. The second pass computes how many nines are needed behind that position (`needStmt_runs`), raises
   the digit and writes the least admissible filling behind it (`fillTail_spec`).  What stands in
   the memory then is `Spec.raiseAt` (`segN_raiseAt`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine











end Nine

open Nine

/-! ## The first pass -/

















private theorem scanRound_cost : scanRound.blockCost = 35 := rfl






/-- One round of the scan is `Spec.nineScanStep`. -/
private theorem scanRound_runs (hs : Std lim) {μ : ℕ → ℤ} {a n lo hi i dg dg' : ℕ} {s : NineScan}
    (ha : a + n < lim.space) (hi' : i < n) (hcell : μ (a + i) = dg) (hnines : s.nines ≤ i) :
    scanRound.Runs lim ⟨scanFrame a n lo hi i s dg', μ⟩
      (· = ⟨scanFrame a n lo hi (i + 1) (nineScanStep hi i dg s) dg, μ⟩) := by
  (obtain ⟨⟩ := id hs)
  have hcast8 : ((dg : ℤ) = 8) = (dg = 8) := by norm_cast
  have hcast9 : ((dg : ℤ) = 9) = (dg = 9) := by norm_cast
  simp only [scanRound, raiseTest, markStmt, scanFrame, nineScanStep, canRaise]
  -- The tests of the program tell five cases apart: the digit is below 8; it is 8, and one more
  -- nine is allowed or not; it is 9; it is above 9.  In each case the block is run: the first goal
  -- says that every address is in range and every value fits in a word, the second that the last
  -- state is the one stated.
  have hcases : (dg < 8 ∧ dg ≠ 8 ∧ dg ≠ 9) ∨ (dg = 8 ∧ s.nines < hi) ∨ (dg = 8 ∧ ¬ s.nines < hi) ∨
      dg = 9 ∨ (¬ dg < 8 ∧ dg ≠ 8 ∧ dg ≠ 9) := by omega
  rcases hcases with ⟨h₁, h₂, h₃⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl | ⟨h₁, h₂, h₃⟩ <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega






/-! ## The second pass -/









private theorem needStmt_cost : needStmt.blockCost = 23 := rfl

/-- needStmt computes the subtraction of natural numbers in `Spec.raiseAt`. -/
private theorem needStmt_runs (hs : Std lim) {μ : ℕ → ℤ} {a n lo hi i dg dg' : ℕ} {s : NineScan}
    (ha : a + n < lim.space) (hp : s.pos < n) (hcell : μ (a + s.pos) = dg) (hlo : lo ≤ n)
    (hbefore : s.before ≤ n) :
    needStmt.Runs lim ⟨scanFrame a n lo hi i s dg', μ⟩
      (· = ⟨frame [a, n, lo, hi, i, s.found, s.pos, s.before, s.nines, dg,
        ((lo - s.before - (if dg = 8 then 1 else 0) : ℕ) : ℤ)], μ⟩) := by
  (obtain ⟨⟩ := id hs)
  have hcast8 : ((dg : ℤ) = 8) = (dg = 8) := by norm_cast
  have hzero₁ : (lo : ℤ) - s.before - 1 < 0 → lo - s.before - 1 = 0 := by omega
  have hcast₁ : ¬ (lo : ℤ) - s.before - 1 < 0 →
      ((lo - s.before - 1 : ℕ) : ℤ) = (lo : ℤ) - s.before - 1 := by omega
  have hzero₀ : (lo : ℤ) - s.before < 0 → lo - s.before = 0 := by omega
  have hcast₀ : ¬ (lo : ℤ) - s.before < 0 → ((lo - s.before : ℕ) : ℤ) = (lo : ℤ) - s.before := by
    omega
  simp only [needStmt, scanFrame]
  -- The tests of the program tell four cases apart: whether the digit is an 8, and whether the
  -- difference that is then formed is negative.  In each case the block is run (first goal:
  -- everything is in range; second goal: the last state is the one stated).
  have hcases : (dg = 8 ∧ (lo : ℤ) - s.before - 1 < 0) ∨ (dg = 8 ∧ ¬ (lo : ℤ) - s.before - 1 < 0) ∨
      (dg ≠ 8 ∧ (lo : ℤ) - s.before < 0) ∨ (dg ≠ 8 ∧ ¬ (lo : ℤ) - s.before < 0) := by omega
  rcases hcases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h₁, h⟩ | ⟨h₁, h⟩ <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- The string with the digits before p kept, the digit at p raised and the least filling behind it
is `Spec.raiseAt`. -/
private theorem segN_raiseAt {μ μ' : ℕ → ℤ} {a lo p c : ℕ} {l : List ℕ} (hseg : SegN μ a l)
    (hp : p < l.length) (hkeep : ∀ b < a + p, μ' b = μ b)
    (hdigit : μ' (a + p) = (l.getD p 0 + 1 : ℕ))
    (htail : SegN μ' (a + (p + 1))
      (nineFirst (l.length - (p + 1)) (lo - c - if l.getD p 0 = 8 then 1 else 0))) :
    SegN μ' a (raiseAt lo p c l) := by
  have hlen : a + (List.map (fun x : ℕ => (x : ℤ)) (l.take p)).length = a + p := by
    rw [List.length_map, List.length_take, min_eq_left hp.le]
  rw [raiseAt, SegN, List.map_append, seg_append, List.map_cons, seg_cons, hlen, Nat.sub_sub,
    List.map_take]
  exact ⟨(hseg.take p).congr fun i hi => hkeep _ (by simp at hi; omega), hdigit, htail⟩










/-- The second pass writes `Spec.raiseAt` for the position that the scan has found, and
returns 1. -/
private theorem raiseStmt_spec (hs : Std lim) {μ : ℕ → ℤ} {a lo hi dg' : ℕ} {l : List ℕ}
    (hseg : SegN μ a l) (ha : a + l.length < lim.space) (hlo : lo ≤ l.count 9)
    (hfound : (nineScan hi l l.length).found = 1) :
    Ends lim P d raiseStmt ⟨scanFrame a l.length lo hi l.length (nineScan hi l l.length) dg', μ⟩
      (15 * l.length + 46) fun σ' =>
        SegN σ'.mem a
          (raiseAt lo (nineScan hi l l.length).pos (nineScan hi l l.length).before l) ∧
        σ'.loc 0 = 1 ∧ SameOutside μ σ'.mem a l.length := by
  (obtain ⟨⟩ := id hs)
  have hinv := nineScan_inv hi l le_rfl
  generalize nineScan hi l l.length = s at hinv hfound ⊢
  have hp := hinv.pos_lt hfound
  have hdigit_le := le_of_canRaise (hinv.canRaise hfound)
  have hfits := raise_fits hp hdigit_le hlo
  rw [← hinv.before hfound] at hfits
  have hbefore : s.before ≤ l.length := by
    rw [hinv.before hfound]
    exact List.count_le_length.trans (List.length_take_le' _ _)
  have hlon : lo ≤ l.length := hlo.trans List.count_le_length
  have hcost := needStmt_cost
  obtain ⟨dg, hdg⟩ : ∃ dg, l.getD s.pos 0 = dg := ⟨_, rfl⟩
  obtain ⟨need, hneed⟩ : ∃ need, lo - s.before - (if dg = 8 then 1 else 0) = need := ⟨_, rfl⟩
  have hneed_le : need ≤ lo - s.before := hneed ▸ Nat.sub_le _ _
  rw [hdg] at hdigit_le
  -- digit := mem[str + best]; need := max (lo - before - [digit = 8]) 0
  refine Ends.next _ (Ends.block
    ((needStmt_runs hs ha hp (hdg ▸ hseg.read hp) hlon hbefore).mono ?_) le_rfl)
  rintro _ rfl
  rw [hneed]
  -- mem[str + best] := digit + 1
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
        Light.Ends.storeToThen (a + s.pos)
          (dg + 1 : ℕ)
            -- pos := best + 1
            
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
  -- pos := best + 1
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
          (s.pos + 1 : ℕ)
            -- fillTail
            
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
  -- fillTail
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
            (fillTail_spec hs (i₀ := s.pos + 1) (need := need) ha (by omega) _ rfl
              rfl rfl rfl)
            ?_ ?_
      |
        refine
          Light.Ends.pieceLast
            (fillTail_spec hs (i₀ := s.pos + 1) (need := need) ha (by omega) _ rfl
              rfl rfl rfl)
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
    (on_goal -1 =>
        rintro ⟨_, μ'⟩
          ⟨rfl, htail, hsame⟩
              -- return 1
              )
  -- return 1
  refine Ends.setLast ⟨segN_raiseAt hseg hp (fun b hb => ?_) ?_ (by rw [hdg, hneed]; exact htail),
    by simp, ?_⟩
  · rw [hsame b (Or.inl (by omega)), Function.update_of_ne (by omega)]
  · rw [hsame _ (Or.inl (by omega)), Function.update_self, hdg]
  · exact (SameOutside.refl.update ⟨by omega, by omega⟩ _).trans (hsame.mono (by omega) (by omega))

/-! ## The routine -/








/-- **nineNext** replaces the string by the next one and returns 1, or leaves the last string and
returns 0. -/
theorem nineNext_spec (hP : P[Proc.nineNext]? = some nineNextBody) (hs : Std lim) :
    NineNextSpec lim P := by
  rintro a _ lo hi l μ hseg hmem ha
  obtain ⟨rfl, -, hlo, -⟩ := (mem_nineStrs l).1 hmem
  refine fun d _ => ⟨nineNextBody, hP, ?_⟩
  (obtain ⟨⟩ := id hs)
  unfold tNineNext
  -- pos := 0
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
          (0 : ℕ)
            -- while pos < len
            
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
  -- while pos < len
  refine Ends.next _ (Ends.whileBlock (ScanInv a lo hi l μ) l.length ?start ?round ?done
    (hT := le_rfl)) (by simp [scanRound_cost]; omega)
  case start => exact ⟨0, congrArg (State.mk · μ) (frame_append_zeros _ 5).symm⟩
  case round =>
    rintro i _ hi' ⟨dg', rfl⟩
    have hnines : (nineScan hi l i).nines ≤ i := by
      rw [(nineScan_inv hi l hi'.le).nines]
      exact List.count_le_length.trans (List.length_take_le _ _)
    exact ⟨by simp, by simp [scanFrame]; omega,
      (scanRound_runs hs ha hi' (hseg.read hi') hnines).mono fun σ' hσ' =>
        ⟨l.getD i 0, by rw [hσ', nineScan_succ hi l hi']⟩⟩
  case done =>
    rintro _ ⟨dg', rfl⟩
    refine ⟨by simp, by simp [scanFrame], ?_⟩
    simp only [scanRound_cost]
    rw [nineNext_eq_scan]
    -- if found = 1
    refine Ends.iteLast (fun hfound => ?_) (fun hfound => ?_) (by simp; omega)
    · have hfound' : (nineScan hi l l.length).found = 1 := by
        simpa [scanFrame] using hfound
      simp only [if_pos hfound', Option.getD_some, Option.isSome_some, if_true]
      exact (raiseStmt_spec hs hseg ha hlo hfound').mono (by first
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
                                                                   | ((ring_nf); (omega)))) fun _ h => h
    · have hfound' : ¬ (nineScan hi l l.length).found = 1 := by
        simpa [scanFrame] using hfound
      simp only [if_neg hfound', Option.getD_none, Option.isSome_none]
      -- return 0
      exact Ends.setLast ⟨hseg, by simp, SameOutside.refl⟩

end Light.Sec4

end
end

section


/-!
# The digits of the output string of a position

Proof of Theorem 30, "Query": "Given (I, J), we find its tile from the bands of row I and column J,
the subset Q of its block product, and its output string w (whose variables at the levels outside Q
we read off the row and column of (I, J) within the block product), all in O(L) operations". The
routine walks the mask of the subset: it writes the digit 9 at a level of the subset (levelInner),
and otherwise 3 x + y for the next base-3 digits x and y of the offsets of I and J (levelOuter). The
invariant OutDigits.Inv says what has been written before level l; each of the two branches takes it
from l to l + 1 (OutDigits.inner, OutDigits.outer).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace OutDigits















end OutDigits




























namespace OutDigits

/-! ## The pure side: the digit at one level -/

variable {lim : Limits} {μ : ℕ → ℤ} {x : OutDigitsArgs} {l : ℕ} {σ : State}

/-- The mask has one entry for each level. -/
theorem length_mask : x.mask.length = x.L := length_unrank ..

/-- The output string has one digit for each level. -/
theorem length_digits : x.digits.length = x.L := length_outDigits.trans length_mask

/-- The digit at a level of the subset. -/
theorem getD_digits_inner (C : OutDigitsPre lim μ x) (hl : l < x.L)
    (hb : x.mask.getD l false = true) : x.digits.getD l 0 = 9 :=
  getD_outDigits_of_true (count_unrank C.index_lt) (length_mask.symm ▸ hl) hb

/-- The digit at a level outside the subset, and the room behind the pointer. -/
theorem getD_digits_outer (C : OutDigitsPre lim μ x) (hl : l < x.L)
    (hb : x.mask.getD l false = false) :
    (x.mask.take l).count false < x.L - x.m ∧
      x.digits.getD l 0 = 3 * x.rI.getD ((x.mask.take l).count false) 0
        + x.rJ.getD ((x.mask.take l).count false) 0 := by
  have hl' : l < x.mask.length := length_mask.symm ▸ hl
  have hcount : x.mask.count false = x.L - x.m := count_false_unrank C.index_lt
  exact ⟨hcount ▸ List.count_take_lt hl' false hb,
    getD_outDigits_of_false (C.lenI.trans hcount.symm) (C.lenJ.trans hcount.symm) hl' hb⟩

/-- The mask of the subset lies inside the table of the K0² masks. -/
theorem base_add_le (C : OutDigitsPre lim μ x) : x.base + x.L < lim.space := by
  have := Nat.mul_add_le_mul (Nat.mul_add_lt_mul C.gI_lt C.gJ_lt) (le_refl x.L)
  have := C.spaceMasks
  unfold OutDigitsArgs.base
  omega

/-! ## The invariant and the two branches -/









/-- The cell of the mask that the test of level l reads. -/
theorem read_mask (C : OutDigitsPre lim μ x) {μ' : ℕ → ℤ} (same : SameOutside μ μ' x.wd x.L)
    (hl : l < x.L) : μ' (x.base + l) = if x.mask.getD l false then 1 else 0 := by
  have hlen := length_mask (x := x)
  have hap := C.apartMask
  rw [same (x.base + l) (by omega), C.segMask.read (by simp [hlen, hl]),
    List.getD_eq_getElem _ _ (by simp [hlen, hl]), List.getElem_map,
    List.getD_eq_getElem _ _ (by omega)]
  split_ifs <;> rfl

/-- wd[level] := 9; level := level + 1. -/
theorem inner (C : OutDigitsPre lim μ x) (h : Inv μ x l σ) (hl : l < x.L)
    (hb : x.mask.getD l false = true) : levelInner.Runs lim σ (Inv μ x (l + 1)) := by
  obtain ⟨μ', rfl, seg, same⟩ := h
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  have hnext := seg.take_succ (length_digits.symm ▸ hl)
  have hcount : (x.mask.take (l + 1)).count false = (x.mask.take l).count false := by
    rw [List.count_take_succ_getD x.mask false (length_mask.symm ▸ hl) false, hb]
    rfl
  rw [getD_digits_inner C hl hb] at hnext
  refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                 ((try have := Light.Std.const_le (by assumption)));
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, levelInner] <;> omega)), _, ?_, hnext,
    same.update ⟨by omega, by omega⟩ _⟩
  simp [levelInner, update_frame_setLocal, hcount]

/-- wd[level] := 3 dI[outer] + dJ[outer]; outer := outer + 1; level := level + 1. -/
theorem outer (C : OutDigitsPre lim μ x) (h : Inv μ x l σ) (hl : l < x.L)
    (hb : x.mask.getD l false = false) : levelOuter.Runs lim σ (Inv μ x (l + 1)) := by
  obtain ⟨μ', rfl, seg, same⟩ := h
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  obtain ⟨hlt, hdigit⟩ := getD_digits_outer C hl hb
  -- the two digits that the level reads
  have hreadI : μ' (x.dI + (x.mask.take l).count false)
      = ((x.rI.getD ((x.mask.take l).count false) 0 : ℕ) : ℤ) := by
    have hap := C.apartI
    rw [same _ (by omega)]
    exact C.segI.read (by have := C.lenI; omega)
  have hreadJ : μ' (x.dJ + (x.mask.take l).count false)
      = ((x.rJ.getD ((x.mask.take l).count false) 0 : ℕ) : ℤ) := by
    have hap := C.apartJ
    rw [same _ (by omega)]
    exact C.segJ.read (by have := C.lenJ; omega)
  have hI3 : x.rI.getD ((x.mask.take l).count false) 0 < 3 :=
    List.getD_of_forall_mem (by norm_num) C.ltI _
  have hJ3 : x.rJ.getD ((x.mask.take l).count false) 0 < 3 :=
    List.getD_of_forall_mem (by norm_num) C.ltJ _
  have hnext := seg.take_succ (length_digits.symm ▸ hl)
  have hcount : (x.mask.take (l + 1)).count false = (x.mask.take l).count false + 1 := by
    rw [List.count_take_succ_getD x.mask false (length_mask.symm ▸ hl) false, if_pos hb]
  rw [hdigit] at hnext
  generalize x.rI.getD ((x.mask.take l).count false) 0 = a at hreadI hI3 hnext
  generalize x.rJ.getD ((x.mask.take l).count false) 0 = b at hreadJ hJ3 hnext
  refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                 ((try have := Light.Std.const_le (by assumption)));
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, levelOuter, hreadI, hreadJ] <;>
                     omega)), _, ?_, hnext,
    same.update ⟨by omega, by omega⟩ _⟩
  simp [levelOuter, update_frame_setLocal, hcount, hreadI, hreadJ]

/-- The walk along the mask writes the digits of the output string. -/
theorem walk {P : Program} {d : ℕ} (C : OutDigitsPre lim μ x) :
    Ends lim P d outDigitsWalk
      ⟨frame [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd, x.base, (0 : ℕ), (0 : ℕ)], μ⟩
      (40 * x.L + 4) fun σ' => SegN σ'.mem x.wd x.digits ∧ SameOutside μ σ'.mem x.wd x.L := by
  (obtain ⟨⟩ := id C.std)
  have hspace := base_add_le C
  refine Ends.whileBlock (Inv μ x) x.L ?start ?round ?done
    (by simp [levelInner, levelOuter]; omega)
  case start => exact ⟨μ, rfl, by simp [SegN, Seg], .refl⟩
  case round =>
    rintro l σ hl hI
    have hinner := inner C hI hl
    have houter := outer C hI hl
    obtain ⟨μ', rfl, -, same⟩ := hI
    have hread := read_mask C same hl
    refine ⟨by simp, by simpa using hl, ?_⟩
    -- if mask[level] = 1
    by_cases hb : x.mask.getD l false = true
    · rw [if_pos hb] at hread
      exact .ite_pos (hinner hb) (by simp [hread]) (by (((try have := Light.Std.space_le (by assumption)));
                                                         ((try have := Light.Std.const_le (by assumption)));
                                                         (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    · rw [if_neg hb] at hread
      exact .ite_neg (houter (by simpa using hb)) (by simp [hread])
        (by (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
  case done =>
    rintro _ ⟨μ', rfl, seg, same⟩
    rw [List.take_of_length_le length_digits.le] at seg
    exact ⟨by simp, by simp, seg, same⟩

/-- The numbers on the way to the address of the mask fit in a word. -/
theorem index_le (C : OutDigitsPre lim μ x) : x.gI * x.k0 + x.gJ ≤ lim.space := by
  have hidx := C.index_lt
  have hbase := base_add_le C
  unfold OutDigitsArgs.base at hbase
  rcases Nat.eq_zero_or_pos x.L with h0 | hL
  · have hm : x.m = 0 := by have := C.m_le; omega
    rw [h0, hm, Nat.choose_self] at hidx
    omega
  · exact (Nat.le_mul_of_pos_right _ hL).trans (by omega)

end OutDigits

open OutDigits in
/-- **outDigits** meets its specification. -/
theorem outDigits_spec {lim : Limits} {P : Program}
    (hP : P[Proc.outDigits]? = some outDigitsBody) : OutDigitsSpec lim P := by
  intro x μ C
  refine fun d _ => ⟨outDigitsBody, hP, ?_⟩
  have hw := C.std.space_le
  have hidx := index_le C
  have hbase := base_add_le C
  have hprod : ((x.gI * x.k0 : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : x.gI * x.k0 ≤ lim.space)
  have haddr : ((x.base : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega : x.base ≤ lim.space)
  have hprod0 : (0 : ℤ) ≤ (x.gI : ℤ) * x.k0 := by positivity
  have hoff0 : (0 : ℤ) ≤ ((x.gI : ℤ) * x.k0 + x.gJ) * x.L := by positivity
  unfold OutDigitsArgs.base at haddr
  push_cast at hprod haddr
  unfold tOutDigits
  -- mask := aMASK + (gI K0 + gJ) L
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen x.base ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                OutDigitsArgs.base]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [OutDigitsArgs.base] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, OutDigitsArgs.base] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- level := 0; outer := 0; the walk
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
  exact (walk C).mono (by simp; omega) fun _ h => h

end Light.Sec4

end
end

section


/-!
# A query, once the digits of its output string are known

Proof of Theorem 30, "Query"; these are steps (2) and (3) of the query in Section 4.3. The routine
adds up the sum of Lemma 28: for each leaf of order below t contributing to the output string the
product of its two numbers in the encodings of the tile (queryLowRound), and for each box of the
output string its value (queryBoxRound): "we look up its value in the trie of the tile". The root of
this trie is an argument of the routine.

Leaves and boxes are enumerated through the strings of m digits with a bounded number of nines. For
the boxes the proof of Theorem 30 says "for every V ⊆ Q with |V| = m - t and every box of 𝓑_V". The
routine has one loop (queryBoxes), over the strings with exactly m - t nines: such a string gives V
(the places of its nines) and the box of 𝓑_V (its other digits) at once. This is the other way in
which Section 4.2 describes the boxes of w, "in terms of the leaves of order exactly t contributing
to w. For such a leaf, consider the lowest level of Q at which it chooses a term other than P₀, and
replace its P₀ by a star at every lower level of Q (or at every level of Q, if t = 0). The result is
a box of w, and each box of w arises exactly once in this way" (for cubes:
`existsUnique_starBelow_eq`). The members of the list of the routine are exactly the strings of the
cubes so obtained (`mem_boxesOf_iff`), and a sum over the list is the sum over the sets 𝓑_V
(`sum_boxesOf`). The sets V come interleaved, in the lexicographic order of the strings.

Both loops have one invariant, Query.Inv: the sum of the first terms stands in a local, and the
current string of the enumeration in the scratch area ss. Query.low_term and Query.box_term say
which term a round adds; Query.lowRound and Query.boxRound are the two rounds, Query.loop is either
loop, and queryCore_spec puts the two loops together.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace Query




















end Query









































namespace Query

/-! ## The pure side: the terms of the sum -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}







/-- The output string has one digit for each level. -/
theorem length_digits (x : QueryCoreArgs) : (digitsO x.η).length = x.L := length_digitsO x.η

/-- The digit 9, which stands at the levels of the subset, occurs m times. -/
theorem count_digits (C : QueryCorePre lim μ x) : (digitsO x.η).count 9 = x.m := by
  rw [← card_innerSetO, C.card]









/-- Round i of the first loop treats a leaf τ and adds the product of its two numbers. -/
theorem low_term (C : QueryCorePre lim μ x) (hi : i < lowCount x) :
    ∃ τ : Leaf x.L, leafAt x i = digitsT τ ∧
      (x.terms.take (i + 1)).sum = (x.terms.take i).sum + x.encA τ * x.encB τ := by
  have hleaf : leafAt x i ∈ lowList x.m x.t (digitsO x.η) :=
    List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩
  obtain ⟨τ, -, hτ⟩ := exists_of_mem_lowList C.card _ hleaf
  refine ⟨τ, hτ.symm, ?_⟩
  have hlen : i < (lowList x.m x.t (digitsO x.η)).length := by simpa [lowList] using hi
  have hmember : (lowList x.m x.t (digitsO x.η))[i] = digitsT τ := by
    rw [hτ]
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [lowList, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms,
    List.getD_append _ _ _ _ (by rwa [List.length_map]),
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember,
    leafProduct_digitsT]

/-- Round i of the second loop treats a box and adds its value, looked up in the trie of the
tile. -/
theorem box_term (hi : i < boxCount x) :
    boxAt x i ∈ boxesOf x.m x.t (digitsO x.η) ∧
      (x.terms.take (lowCount x + (i + 1))).sum = (x.terms.take (lowCount x + i)).sum +
        trieLookup x.T x.root (boxAt x i) := by
  refine ⟨List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩, ?_⟩
  have hlows : ((lowList x.m x.t (digitsO x.η)).map
      (leafProduct (arrT x.encA) (arrT x.encB))).length = lowCount x := by simp [lowList]
  have hlen : i < (boxesOf x.m x.t (digitsO x.η)).length := by simpa [boxesOf] using hi
  have hmember : (boxesOf x.m x.t (digitsO x.η))[i] = boxAt x i := by
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [boxesOf, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [← Nat.add_assoc, List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms, ← hlows,
    List.getD_append_add,
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember]

/-! ## The memory and the invariant -/

section Same

variable {μ₁ μ₂ : ℕ → ℤ} {ss m box L a : ℕ} {l : List ℤ}

/-- A write to the string at ss stays within the two scratch strings. -/
theorem same_of_ss (h : SameOutside2 μ μ₁ ss m box L) (h' : SameOutside μ₁ μ₂ ss m) :
    SameOutside2 μ μ₂ ss m box L := h.then h' fun _ hb => ⟨hb, hb.1⟩

/-- A write to the string at box stays within the two scratch strings. -/
theorem same_of_box (h : SameOutside2 μ μ₁ ss m box L) (h' : SameOutside μ₁ μ₂ box L) :
    SameOutside2 μ μ₂ ss m box L := h.then h' fun _ hb => ⟨hb, hb.2⟩

/-- A segment that meets neither scratch string is kept. -/
theorem seg_of_same (h : SameOutside2 μ μ₁ ss m box L) (hl : Seg μ a l)
    (h1 : Apart ss m a l.length) (h2 : Apart box L a l.length) : Seg μ₁ a l :=
  hl.of_sameOn h fun i hi => ⟨by omega, by omega⟩

end Same



















variable {σ : State}

/-- The digits of the output string are kept. -/
theorem segDigits (C : QueryCorePre lim μ x) {μ' : ℕ → ℤ}
    (same : SameOutside2 μ μ' x.ss x.m x.box x.L) :
    SegN μ' x.wd (digitsO x.η) :=
  seg_of_same same C.segDigits (by simpa [length_digits] using C.ss_wd)
    (by simpa [length_digits] using C.box_wd)

/-! ## The two calls that both rounds make -/

section Calls

variable {lo hi : ℕ} {μ₀ : ℕ → ℤ}

/-- scatter(wd, ss, box, L, star) writes the leaf or the box of string number i at box; the string
at ss is kept. -/
theorem scatter_meets (K : Callees lim P) (C : QueryCorePre lim μ x) (star : Bool)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.scatter d [x.wd, x.ss, x.box, x.L, if star then 1 else 0] μ₀ (tScatter x.L)
      fun _ μ₁ => SegN μ₁ x.box (scatter (digitsO x.η) (starRunIf star (nineStr x.m lo hi i))) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  obtain ⟨hlen, -⟩ := (mem_nineStrs _).mp (nineStr_mem hstr)
  have hapart := C.ss_box
  refine (K.scatter x.wd x.ss x.box x.L star (digitsO x.η) _ μ₀ (segDigits C same) hss
    (length_digits x) (by rw [hlen, count_digits C]) C.box_wd
    (by omega) C.wd_lt (by rw [hlen]; exact C.ss_lt) C.box_lt _
      (by omega)).mono le_rfl fun _ μ₁ ⟨hbox, same₁⟩ => ⟨hbox, ?_, same_of_box same same₁⟩
  exact hss.of_sameOutside same₁ (by omega)

/-- nineNext(ss, m, lo, hi) goes on to string number i + 1 and says whether there is one. -/
theorem next_meets (K : Callees lim P) (C : QueryCorePre lim μ x)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.nineNext d [x.ss, x.m, lo, hi] μ₀ (tNineNext x.m) fun r μ₁ =>
      r = (if i + 1 < (nineStrs x.m lo hi).length then 1 else 0) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi (i + 1)) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  refine (K.nineNext x.ss x.m lo hi _ μ₀ hss (nineStr_mem hstr) C.ss_lt _ (by omega)).mono le_rfl
    fun r μ₁ ⟨hss₁, hr, same₁⟩ => ⟨?_, nineStr_succ .. ▸ hss₁, same_of_ss same same₁⟩
  rw [hr, isSome_nineNext_nineStr hstr]
  simp

end Calls

/-! ## The two rounds -/

/-- One round of the first loop adds the term of the leaf number i. -/
theorem lowRound (K : Callees lim P) (C : QueryCorePre lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < lowCount x) (h : Inv μ x (x.m - x.t + 1) x.m 0 i σ) :
    Ends lim P d queryLowRound σ (tScatter x.L + tHorner x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t + 1) x.m 0 (i + 1)) := by
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  obtain ⟨τ, hτ, hsum⟩ := low_term C hi
  -- code := scatter(wd, ss, box, L, 0): the leaf
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
            ((scatter_meets K C false hi hss same (by omega)) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (scatter_meets K C false hi hss same (by omega))
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
        ((rintro _ μ₁ ⟨hbox, hss₁, same₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  replace hbox : SegN μ₁ x.box (digitsT τ) := hτ ▸ hbox
  -- code := horner(box, L)
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
            ((K.horner x.box x.L (digitsT τ) μ₁ hbox (length_digitsT τ)
                (digitsT_lt τ) C.box_lt C.pow _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.horner x.box x.L (digitsT τ) μ₁ hbox (length_digitsT τ)
              (digitsT_lt τ) C.box_lt C.pow _ (by omega))
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
        ((rintro _ μ' ⟨rfl, hμ'⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain rfl : μ₁ = μ' := hμ'.symm
  rw [ofDigitList_digitsT]
  -- sum := sum + aA[code] * aB[code]
  have hcode : codeT τ < 10 ^ x.L := codeT_lt τ
  (obtain ⟨⟩ := id C)
  have hreadA : μ₁ (x.aA + codeT τ) = x.encA τ := by
    rw [(seg_of_same same₁ C.segA (by simpa [length_arrT] using C.ss_aA)
      (by simpa [length_arrT] using C.box_aA)).getD (by rw [length_arrT]; exact hcode) 0, getD_arrT]
  have hreadB : μ₁ (x.aB + codeT τ) = x.encB τ := by
    rw [(seg_of_same same₁ C.segB (by simpa [length_arrT] using C.ss_aB)
      (by simpa [length_arrT] using C.box_aB)).getD (by rw [length_arrT]; exact hcode) 0, getD_arrT]
  have hprod := abs_le.1 (C.prod τ)
  have hfits := abs_le.1 (C.sums (i + 1))
  rw [hsum] at hfits
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
        Light.Ends.setToThen ((x.terms.take i).sum + x.encA τ * x.encB τ) ?_ ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hreadA,
                hreadB]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadA, hreadB] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadA, hreadB] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- more := nineNext(ss, m, m - t + 1, m)
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
            ((next_meets K C hi hss₁ same₁ (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (next_meets K C hi hss₁ same₁ (by omega)) ?_ ?_ ?_
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
        ((rintro _ μ₂ ⟨rfl, hss₂, same₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨codeT τ, value, μ₂, by simp [hsum], hss₂, same₂⟩

/-- One round of the second loop adds the value of the box number i. -/
theorem boxRound (K : Callees lim P) (C : QueryCorePre lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < boxCount x) (h : Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) i σ) :
    Ends lim P d queryBoxRound σ (tScatter x.L + tLookup x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) (i + 1)) := by
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  (obtain ⟨⟩ := id C.std)
  -- what is known about the box
  obtain ⟨hbox, hsum⟩ := box_term hi
  obtain ⟨π, -, hπ⟩ := exists_of_mem_boxesOf C.t_le C.card _ hbox
  have hlen : (boxAt x i).length = x.L := by rw [boxAt, length_scatter, length_digits]
  -- code := scatter(wd, ss, box, L, 1): the box
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
            ((scatter_meets K C true hi hss same (by omega)) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (scatter_meets K C true hi hss same (by omega)) ?_
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro void μ₁
              ⟨hbox₁, hss₁, same₁⟩
                  -- value := lookup(tr, root, box, L)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- value := lookup(tr, root, box, L)
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
            ((K.lookup x.tr x.root x.box x.L x.T (boxAt x i) μ₁
                (seg_of_same same₁ C.segT C.ss_tr C.box_tr) hbox₁ hlen
                (hπ ▸ digitsC_lt π) (C.walk _ hbox) C.tr_lt C.box_lt _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.lookup x.tr x.root x.box x.L x.T (boxAt x i) μ₁
              (seg_of_same same₁ C.segT C.ss_tr C.box_tr) hbox₁ hlen
              (hπ ▸ digitsC_lt π) (C.walk _ hbox) C.tr_lt C.box_lt _ (by omega))
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
        ((rintro _ μ' ⟨rfl, hμ'⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain rfl : μ₁ = μ' := hμ'.symm
  -- sum := sum + value
  have hfits := abs_le.1 (C.sums (lowCount x + (i + 1)))
  rw [hsum] at hfits
  generalize trieLookup x.T x.root (boxAt x i) = val at *
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
          ((x.terms.take (lowCount x + i)).sum + val)
            -- more := nineNext(ss, m, m - t, m - t)
            
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
  -- more := nineNext(ss, m, m - t, m - t)
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
            ((next_meets K C hi hss₁ same₁ (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (next_meets K C hi hss₁ same₁ (by omega)) ?_ ?_ ?_
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
        ((rintro _ μ₂ ⟨rfl, hss₂, same₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨void, val, μ₂, by simp [hsum], hss₂, same₂⟩

/-! ## The two loops -/

/-- Either loop: as long as there is a further string, one round. -/
theorem loop (C : QueryCorePre lim μ x) {round : Stmt} {lo hi base b : ℕ}
    (hround : ∀ i σ, i < (nineStrs x.m lo hi).length → Inv μ x lo hi base i σ →
      Ends lim P d round σ (b + 31) (Inv μ x lo hi base (i + 1)))
    (h : Inv μ x lo hi base 0 σ) :
    Ends lim P d (.while ((Light.Cond.eq (v More) (k 1))) round) σ ((nineStrs x.m lo hi).length * (b + 90) + 4)
      (Inv μ x lo hi base (nineStrs x.m lo hi).length) := by
  have hc := C.std.const_le
  have htime := Nat.mul_le_mul_left (nineStrs x.m lo hi).length
    (show 1 + 1 + 1 + 1 + (b + 31) ≤ b + 90 by omega)
  refine Ends.whileConst (Inv μ x lo hi base) (nineStrs x.m lo hi).length (b + 31) h ?round ?done
    (by simp only [Cond.cost, Expr.cost]; omega)
  case round =>
    rintro i σ hi hI
    have hends := hround i σ hi hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI
    exact ⟨by simp; omega, by simp [hi], hends⟩
  case done =>
    rintro σ hI
    have hI' := hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI'
    exact ⟨by simp; omega, by simp, hI⟩







/-- After a loop, only the sum and the memory matter. -/
theorem Inv.mid {lo hi base : ℕ} (h : Inv μ x lo hi base i σ) : Mid μ x (base + i) σ := by
  obtain ⟨code, value, μ', rfl, -, same⟩ := h
  exact ⟨_, code, value, μ', rfl, same⟩

/-- The leaves of order below t. -/
theorem low_spec (K : Callees lim P) (C : QueryCorePre lim μ x) (hd : d + 1 ≤ lim.depth)
    (ht : 1 ≤ x.t) (h : Mid μ x 0 σ) :
    Ends lim P d queryLow σ
      (tNineFirst x.m + lowCount x * (tScatter x.L + tHorner x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x)) := by
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  have htm := C.t_le
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  have hpos : 0 < lowCount x := length_nineStrs_pos (by omega) (by omega)
  -- nineFirst(ss, m, m - t + 1); more := 1
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
            ((K.nineFirst x.ss x.m (x.m - x.t + 1) μ₀ (by omega) C.ss_lt _
                (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.nineFirst x.ss x.m (x.m - x.t + 1) μ₀ (by omega) C.ss_lt _
              (by omega))
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
        ((rintro _ μ₁ ⟨hss, same₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
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
            -- the loop
            
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
  -- the loop
  refine (loop C (b := tScatter x.L + tHorner x.L + tNineNext x.m)
    (fun i σ hi hI => lowRound K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [lowCount]; omega)
    fun σ' hI => ?_
  simpa using hI.mid

/-- The boxes. -/
theorem boxes_spec (K : Callees lim P) (C : QueryCorePre lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d queryBoxes σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x + boxCount x)) := by
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  (obtain ⟨⟩ := id C.std)
  have hpos : 0 < boxCount x := length_nineStrs_pos (by omega) le_rfl
  -- nineFirst(ss, m, m - t); more := 1
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
            ((K.nineFirst x.ss x.m (x.m - x.t) μ₀ (by omega) C.ss_lt _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (K.nineFirst x.ss x.m (x.m - x.t) μ₀ (by omega) C.ss_lt _ (by omega))
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
        ((rintro _ μ₁ ⟨hss, same₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
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
            -- the loop
            
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
  -- the loop
  exact (loop C (b := tScatter x.L + tLookup x.L + tNineNext x.m)
    (fun i σ hi hI => boxRound K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [boxCount]; omega)
    fun σ' hI => hI.mid

/-- The boxes, and the result. -/
theorem tail_spec (K : Callees lim P) (C : QueryCorePre lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d ((Light.Stmt.seq queryBoxes (.set EncA (v Sum)))) σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 18)
      fun σ' =>
      σ'.loc 0 = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
        SameOutside2 μ σ'.mem x.ss x.m x.box x.L := by
  -- the boxes
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (boxes_spec K C hd h) ?_ ?_
      | refine Light.Ends.pieceLast (boxes_spec K C hd h) ?_ ?_);
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
    (on_goal -1 => rintro _ ⟨more, code, value, μ', rfl, same⟩)
  have hlen : x.terms.length = lowCount x + boxCount x := by
    simp [QueryCoreArgs.terms, queryTerms, lowList, boxesOf]
  have hall : (x.terms.take (lowCount x + boxCount x)).sum
      = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) := by
    rw [← hlen, List.take_length, QueryCoreArgs.terms, trieQuery]
  rw [hall]
  generalize trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) = result
  -- return sum
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen result ?_ ?_ ?_);
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
  exact ⟨rfl, same⟩

end Query

open Query in
/-- **queryCore** meets its specification. -/
theorem queryCore_spec {lim : Limits} {P : Program} (hP : P[Proc.queryCore]? = some queryCoreBody)
    (K : Callees lim P) : QueryCoreSpec lim P := by
  intro x μ C
  refine fun d hd => ⟨queryCoreBody, hP, ?_⟩
  have htm := C.t_le
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.std))
  have hlows : (lowList x.m x.t ([] : List ℕ)).length = lowCount x := by simp [lowList]
  have hboxes : (boxesOf x.m x.t ([] : List ℕ)).length = boxCount x := by simp [boxesOf]
  unfold tQueryCore
  rw [hlows, hboxes]
  -- nines := m - t
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.m - x.t : ℕ) ?_ ?_ ?_);
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
  have hstart : Mid μ x 0 ⟨frame (setLocal [(x.aA : ℤ), x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L,
      x.m, x.t] Nines (x.m - x.t : ℕ)), μ⟩ := ⟨0, 0, 0, μ, by simp, .refl⟩
  -- if t = 0 there are no leaves of order below t
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
        Light.Ends.iteIffThen (x.t = 0) (fun ht0 => ?_) (fun ht1 => ?_) ?_ ?_);
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
    (all_goals
        repeat
          with_unfolding_none
            first
            | refine Light.Ends.seqAssoc ?_
            | refine Light.Ends.skipThen ?_)
  · have hnone : lowCount x = 0 := by
      rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
      intro l hl
      obtain ⟨-, -, hmin, hmax⟩ := (mem_nineStrs l).mp hl
      omega
    focus
      ((refine
            Light.Ends.pieceLast (tail_spec K C hd (hnone ▸ hstart))
              (fun _ apspMacro_283546_0 => apspMacro_283546_0) ?_);
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
                  | ((ring_nf); (omega)))))
  · -- the leaves of order below t, then the boxes
    focus
      (repeat
          with_unfolding_none
            first
            | refine Light.Ends.seqAssoc ?_
            | refine Light.Ends.skipThen ?_);
      (first
        | refine Light.Ends.pieceThen (low_spec K C hd (by omega) hstart) ?_ ?_
        | refine Light.Ends.pieceLast (low_spec K C hd (by omega) hstart) ?_ ?_);
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
      (on_goal -1 => rintro σ' hmid)
    focus
      ((refine
            Light.Ends.pieceLast (tail_spec K C hd hmid)
              (fun _ apspMacro_283718_0 => apspMacro_283718_0) ?_);
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
                  | ((ring_nf); (omega)))))

end Light.Sec4

end
end

section


/-!
# A string put at the levels of the inner set

Proof of Theorem 30: a query forms each leaf or box "from the private leaf".  The output string is
the list of its L digits, and the levels of its inner set are the positions of the digit 9.  The
routine copies this list and replaces its digits 9, from the left, by the digits of a second string
(`Spec.scatter`).  If star = 1, the leading digits 9 of the second string (the levels of F_V,
Section 4.2) are written as stars (`Spec.starRunIf`).

One pass, with a pointer into the second string and a flag that says whether the leading run of
nines is still going on.  `Scatter.scatter_step` says what the first digit of
`scatter w (starRunIf flag s)` is and how the rest looks, in terms of the digit, the flag and the
pointer that the program computes (`outDigit`, `nextRun`, `nextPtr`); `Scatter.round_runs` says
that a round of the program computes them.  The invariant (`Scatter.Inv`) is that the digits written
so far, followed by what is still to be written, are the whole string.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Scatter

/-! ## One more digit -/












/-- The first digit of what is still to be written, and the rest. -/
private theorem scatter_step {w s : List ℕ} {i o : ℕ} (run : ℕ) (hi : i < w.length)
    (ho : w.getD i 0 = 9 → o < s.length) :
    scatter (w.drop i) (starRunIf (decide (run = 1)) (s.drop o)) =
      outDigit (w.getD i 0) (s.getD o 0) run :: scatter (w.drop (i + 1))
        (starRunIf (decide (nextRun (w.getD i 0) (s.getD o 0) run = 1))
          (s.drop (nextPtr (w.getD i 0) o))) := by
  rw [List.drop_eq_getElem_cons hi, ← List.getD_eq_getElem w 0 hi]
  generalize w.getD i 0 = x at ho ⊢
  by_cases hx : x = 9
  · rw [List.drop_eq_getElem_cons (ho hx), ← List.getD_eq_getElem s 0 (ho hx), hx]
    generalize s.getD o 0 = y
    by_cases hy : y = 9
    · rw [hy, starRunIf_nine_cons, scatter_nine_cons]
      by_cases hrun : run = 1 <;> simp [outDigit, nextRun, nextPtr, hrun]
    · rw [starRunIf_cons_of_ne hy, scatter_nine_cons]
      simp [outDigit, nextRun, nextPtr, hy]
  · rw [scatter_cons_of_ne hx]
    simp [outDigit, nextRun, nextPtr, hx]










theorem Progress.zero (star : Bool) (wl sl : List ℕ) :
    Progress star wl sl 0 (if star then 1 else 0) 0 [] :=
  ⟨rfl, rfl, by cases star <;> rfl⟩

section

variable {star : Bool} {wl sl done : List ℕ} {i run o : ℕ}

/-- At a nine of the first string the pointer is inside the second string. -/
theorem Progress.ptr_lt (h : Progress star wl sl i run o done) (hi : i < wl.length)
    (hsl : sl.length = wl.count 9) (h9 : wl.getD i 0 = 9) : o < sl.length := by
  have hle : (wl.take (i + 1)).count 9 ≤ wl.count 9 := (List.take_sublist _ _).count_le _
  rw [List.count_take_succ_getD wl 9 hi 0, if_pos h9, ← h.ptr] at hle
  omega

/-- One more position: the digit, the flag and the pointer are those that the three functions
give. -/
theorem Progress.succ (h : Progress star wl sl i run o done) (hi : i < wl.length)
    (hsl : sl.length = wl.count 9) :
    Progress star wl sl (i + 1) (nextRun (wl.getD i 0) (sl.getD o 0) run)
      (nextPtr (wl.getD i 0) o) (done ++ [outDigit (wl.getD i 0) (sl.getD o 0) run]) where
  length := by rw [List.length_append, h.length, List.length_singleton]
  ptr := by
    rw [List.count_take_succ_getD wl 9 hi 0, ← h.ptr, nextPtr]
    split_ifs <;> rfl
  rest := by
    rw [List.append_assoc, List.singleton_append, ← scatter_step run hi (h.ptr_lt hi hsl)]
    exact h.rest

end

/-! ## The program -/













end Scatter

open Scatter



















namespace Scatter

private theorem round_cost : scatterRound.blockCost = 37 := rfl

/-- What a round does, for the digit x of the first string and the digit y of the second string at
the pointer. -/
private theorem round_runs {lim : Limits} (hs : Std lim) {μ : ℕ → ℤ}
    {w s out L run i o dg x y : ℕ} (hw : w + L < lim.space) (hout : out + L < lim.space)
    (hi : i < L) (hx : μ (w + i) = x) (hy : x = 9 → μ (s + o) = y ∧ s + o + 1 < lim.space) :
    scatterRound.Runs lim ⟨frame [w, s, out, L, run, i, o, dg], μ⟩
      (· = ⟨frame [w, s, out, L, nextRun x y run, (i + 1 : ℕ), nextPtr x o, outDigit x y run],
        Function.update μ (out + i) (outDigit x y run)⟩) := by
  (obtain ⟨⟩ := id hs)
  have hcastx : ((x : ℤ) = 9) = (x = 9) := by norm_cast
  have hcasty : ((y : ℤ) = 9) = (y = 9) := by norm_cast
  have hcastr : ((run : ℤ) = 1) = (run = 1) := by norm_cast
  have haddr : ((out : ℤ) + i).toNat = out + i := by omega
  simp only [scatterRound, outDigit, nextRun, nextPtr]
  -- The tests of the program: a nine of the first string, a nine of the second, the flag.  In each
  -- case the block is run: the first goal says that every address is in range and every value fits
  -- in a word, the second that the last state is the one stated.
  by_cases h9 : x = 9
  · obtain ⟨hcell, hptr⟩ := hy h9
    by_cases hy9 : y = 9 <;> by_cases hrun : run = 1 <;> constructor <;>
      simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
      omega
  · constructor <;> simp [Limits.Addr, abs_le, update_frame_setLocal, *]
    omega







end Scatter

/-- **scatter** writes `Spec.scatter wl (starRunIf star sl)`. -/
theorem scatter_spec {lim : Limits} {P : Program} (hP : P[Proc.scatter]? = some scatterBody)
    (hs : Std lim) : ScatterSpec lim P := by
  rintro w s out _ star wl sl μ hfirst hsecond rfl hsl hapartW hapartS hw_in hs_in hout_in
  refine fun d _ => ⟨scatterBody, hP, ?_⟩
  unfold tScatter
  -- while pos < len
  refine Ends.whileBlock (Inv w s out star wl sl μ) wl.length ?start ?round ?done
    (by simp [round_cost]; omega)
  case start =>
    refine ⟨μ, _, 0, 0, [], ?_, Progress.zero star wl sl, Seg.nil, .refl⟩
    refine congrArg (State.mk · μ) ((frame_append_zeros _ 3).symm.trans ?_)
    cases star <;> rfl
  case round =>
    rintro i _ hi ⟨μ', run, o, dg, done, rfl, hprog, hdone, hsame⟩
    have hx : μ' (w + i) = (wl.getD i 0 : ℕ) :=
      (hsame _ (by omega)).trans (hfirst.read hi)
    have hy : wl.getD i 0 = 9 → μ' (s + o) = (sl.getD o 0 : ℕ) ∧ s + o + 1 < lim.space :=
      fun h9 => by
        have hptr := hprog.ptr_lt hi hsl h9
        exact ⟨(hsame _ (by omega)).trans (hsecond.read hptr), by omega⟩
    refine ⟨by simp, by simp; omega, (round_runs hs hw_in hout_in hi hx hy).mono fun σ' hσ' =>
      ⟨_, _, _, _, _, hσ', hprog.succ hi hsl, ?_, hsame.update ⟨by omega, by omega⟩ _⟩⟩
    have hsnoc := hdone.snoc (outDigit (wl.getD i 0) (sl.getD o 0) run)
    rwa [hprog.length] at hsnoc
  case done =>
    rintro _ ⟨μ', run, o, dg, done, rfl, hprog, hdone, hsame⟩
    have hall : done = scatter wl (starRunIf star sl) := by
      have hrest := hprog.rest
      rwa [List.drop_length, scatter, List.append_nil] at hrest
    exact ⟨by simp, by simp, hall ▸ hdone, hsame⟩

end Light.Sec4

end
end

section


/-!
# The lowest symbols P₀ of a leaf turned into stars

Proof of Lemma 29: "A box in which f of the symbols are P₀ or stars is obtained from a leaf of order
m - f […] by turning the e lowest symbols P₀ of that leaf into stars, for some e ≤ f."  The routine
copies a string of L digits and writes 10 (the star) in place of its first e digits 9
(`Spec.starFirst`).  It returns the position of the last star of the copy, "the highest level at
which π has a star" (proof of Lemma 29), which the dynamic program of Lemma 29 expands
(`Spec.lastStar`).

One pass that keeps two numbers: how many nines have been turned into stars so far, and the
position of the last star so far.  The first section says how one more digit changes the copy and
the two numbers; `StarFirst.round_runs` says that a round of the program does just this;
`StarFirst.Inv` is the invariant of the loop.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One more digit -/

/-- The last star of a list with one more digit. -/
private theorem lastStar_concat (l : List ℕ) (x : ℕ) :
    lastStar (l ++ [x]) = if x = 10 then some l.length else lastStar l := by
  induction l with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [List.cons_append, lastStar, ih, lastStar]
    by_cases hx : x = 10
    · simp [hx]
    · simp only [hx, if_false]

namespace StarFirst

variable {e i : ℕ} {l : List ℕ}







/-- The digit of the copy: a nine becomes a star as long as fewer than e nines have been turned. -/
private theorem getD_starFirst_eq (e : ℕ) (l : List ℕ) (i : ℕ) :
    (starFirst e l).getD i 0 = if l.getD i 0 = 9 ∧ turned e l i < e then 10 else l.getD i 0 := by
  rw [getD_starFirst, turned]
  simp

private theorem turned_zero : turned e l 0 = 0 := by simp [turned]

/-- One more digit: a nine is turned as long as fewer than e have been. -/
private theorem turned_succ (hi : i < l.length) :
    turned e l (i + 1) = if l.getD i 0 = 9 ∧ turned e l i < e then turned e l i + 1
      else turned e l i := by
  rw [turned, turned, List.count_take_succ_getD l 9 hi 0]
  split_ifs <;> omega

/-- One more digit: a star moves the position of the last star. -/
private theorem lastPos_succ (hi : i < l.length) :
    lastPos e l (i + 1) = if (starFirst e l).getD i 0 = 10 then i else lastPos e l i := by
  have hi' : i < (starFirst e l).length := by rwa [length_starFirst]
  rw [lastPos, lastPos, List.take_succ_getD _ hi' 0, lastStar_concat, List.length_take,
    Nat.min_eq_left hi'.le]
  split_ifs <;> rfl

/-! ## The program -/














end StarFirst

open StarFirst

















namespace StarFirst

private theorem round_cost : starFirstRound.blockCost = 34 := rfl

/-- What a round does, for the digit x that is read, with c nines turned and the last star at p. -/
private theorem round_runs {lim : Limits} (hs : Std lim) {μ : ℕ → ℤ} {cur box L e i p x dg c : ℕ}
    (hcur : cur + L < lim.space) (hbox : box + L < lim.space) (hi : i < L) (hc : c ≤ i)
    (hcell : μ (cur + i) = x) :
    starFirstRound.Runs lim ⟨frame [cur, box, L, e, i, p, dg, c], μ⟩
      (· = ⟨frame [cur, box, L, e, (i + 1 : ℕ),
          ((if (if x = 9 ∧ c < e then 10 else x) = 10 then i else p : ℕ) : ℤ),
          ((if x = 9 ∧ c < e then 10 else x : ℕ) : ℤ),
          ((if x = 9 ∧ c < e then c + 1 else c : ℕ) : ℤ)],
        Function.update μ (box + i) ((if x = 9 ∧ c < e then 10 else x : ℕ) : ℤ)⟩) := by
  (obtain ⟨⟩ := id hs)
  have hcast9 : ((x : ℤ) = 9) = (x = 9) := by norm_cast
  have hcast10 : ((x : ℤ) = 10) = (x = 10) := by norm_cast
  have haddr : ((box : ℤ) + i).toNat = box + i := by omega
  simp only [starFirstRound]
  -- The tests of the program: a nine, fewer than e turned, a star.  In each case the block is run:
  -- the first goal says that every address is in range and every value fits in a word, the second
  -- that the last state is the one stated.
  by_cases h9 : x = 9 <;> by_cases hlt : c < e <;> by_cases h10 : x = 10 <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega








end StarFirst

/-- **starFirst** writes the copy with the first e nines as stars, and returns the position of its
last star. -/
theorem starFirst_spec {lim : Limits} {P : Program} (hP : P[Proc.starFirst]? = some starFirstBody)
    (hs : Std lim) : StarFirstSpec lim P := by
  rintro cur box _ e l μ hseg rfl hapart hcur hbox
  refine fun d _ => ⟨starFirstBody, hP, ?_⟩
  have hlen : (starFirst e l).length = l.length := length_starFirst e l
  unfold tStarFirst
  -- while pos < len
  refine Ends.next _ (Ends.whileBlock (Inv cur box e l μ) l.length ?start ?round ?done
    (hT := le_rfl)) (by simp [round_cost]; omega)
  case start =>
    refine ⟨μ, 0, ?_, Seg.nil, .refl⟩
    rw [turned_zero]
    exact congrArg (State.mk · μ) (frame_append_zeros _ 4).symm
  case round =>
    rintro i _ hi ⟨μ', dg, rfl, hcopy, hsame⟩
    have hcell : μ' (cur + i) = (l.getD i 0 : ℕ) :=
      (hsame _ (by omega)).trans (hseg.read hi)
    have hturned : turned e l i ≤ i :=
      (min_le_right _ _).trans (List.count_le_length.trans (List.length_take_le _ _))
    refine ⟨by simp, by simp; omega,
      (round_runs hs hcur hbox hi hturned hcell).mono fun σ' hσ' => ?_⟩
    rw [← getD_starFirst_eq, ← turned_succ hi, ← lastPos_succ hi] at hσ'
    refine ⟨_, _, hσ', ?_, hsame.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hcopy.snoc ((starFirst e l).getD i 0)
    rwa [List.length_take, hlen, Nat.min_eq_left hi.le,
      ← List.take_succ_getD _ (hlen ▸ hi) 0] at hsnoc
  case done =>
    rintro _ ⟨μ', dg, rfl, hcopy, hsame⟩
    rw [← hlen, List.take_length] at hcopy
    refine ⟨by simp, by simp, ?_⟩
    simp only [round_cost]
    -- return last
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (lastPos e l l.length) ?_ ?_ ?_);
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
    refine ⟨hcopy, ?_, hsame⟩
    rw [lastPos, ← hlen, List.take_length]
    rfl

end Light.Sec4

end
end

section


/-!
# The value of a box with stars (proof of Lemma 29, "The values")

"For a box π with e ≥ 1 stars, let ℓ be the highest level at which π has a star.  The leaves of π
are the leaves of the ten strings π[ℓ ← λ] obtained by replacing that star by a term λ, and each of
these strings is again a box, with e - 1 stars. […] Hence we compute val(π) = ∑_λ val(π[ℓ ← λ]) with
ten lookups in the trie, in O(L) operations."  The routine writes the ten digits one after the other
at the position of the star, looks each string up, adds, and puts the star back.  It looks in the
trie of the tile, which is being filled.

Before round j the sum of the first j values has been formed, and the memory differs from the
original one at the position of the star only (`SumTen.Inv`).  `SumTenPre` collects what the
routine assumes.  In a round the string with the digit j at the position of the star stands in the
memory (`segN_set`), so lookup returns its value (`SumTen.round_spec`); `sumTen_spec` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace SumTen















end SumTen


















/-- A string with one digit replaced, in the memory. -/
private theorem segN_set {μ μ' : ℕ → ℤ} {a p : ℕ} {l : List ℕ} (h : SegN μ a l)
    (hp : p < l.length) (x : ℕ) (hx : μ' (a + p) = x) (ho : ∀ b, b ≠ a + p → μ' b = μ b) :
    SegN μ' a (l.set p x) := by
  intro i hi
  have hi' : i < l.length := by simpa using hi
  by_cases hip : i = p
  · subst hip
    simp [hx]
  · rw [ho _ (by omega), SegN.getElem h hi']
    simp [List.getElem_set_of_ne (Ne.symm hip)]

namespace SumTen











/-- One round adds the value of the string with the digit j.  The conclusion has the form that the
rule for counting loops asks for: the loop itself then raises the digit. -/
private theorem round_spec {lim : Limits} {P : Program} {d : ℕ} (hLookup : LookupSpec lim P)
    (hs : Std lim) {x : SumTenArgs} {saved j : ℕ} {val : ℤ} {μ μ' : ℕ → ℤ}
    (C : SumTenPre lim μ x) (hdep : d + 1 ≤ lim.depth) (hj : j < 10)
    (hsame : SameOn (· ≠ x.box + x.p) μ μ') :
    Ends lim P d sumTenRound
      ⟨frame [x.tr, x.root, x.box, x.l.length, x.p, saved, j, (x.values.take j).sum, val], μ'⟩
      (tRound x.l.length) fun σ' => σ'.loc Digit = j ∧
        Inv x saved μ (j + 1) { σ' with loc := Function.update σ'.loc Digit ((j : ℤ) + 1) } := by
  have hp := C.star
  have hboxB := C.box_in
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id hs))
  have hsum := C.sums (j + 1) (by omega)
  unfold tRound
  -- mem[box + star] := digit
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (x.box + x.p) j ?_ ?_ ?_);
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
  have hsame₁ : SameOn (· ≠ x.box + x.p) μ (Function.update μ' (x.box + x.p) j) :=
    hsame.write (by simp) _
  have hdigits : ∀ d ∈ x.l.set x.p j, d < 11 := fun d hd => by
    rcases List.mem_or_eq_of_mem_set hd with h | h
    · exact C.digits d h
    · omega
  -- val := lookup(area, root, box, len)
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
            ((hLookup x.tr x.root x.box x.l.length x.T (x.l.set x.p j) _
                C.area.keep
                (segN_set C.seg hp j (Function.update_self _ _ _) hsame₁)
                (by simp) hdigits (C.walk j hj) C.area_in hboxB _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hLookup x.tr x.root x.box x.l.length x.T (x.l.set x.p j) _
              C.area.keep
              (segN_set C.seg hp j (Function.update_self _ _ _) hsame₁) (by simp)
              hdigits (C.walk j hj) C.area_in hboxB _ (by omega))
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
        ((rintro _ _ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hnext : (x.values.take (j + 1)).sum
      = (x.values.take j).sum + trieLookup x.T x.root (x.l.set x.p j) :=
    List.sum_take_map_range_succ (fun d => trieLookup x.T x.root (x.l.set x.p d)) hj
  rw [hnext] at hsum
  -- sum := sum + val
  exact Ends.setTo _ ⟨by simp, _, _, by rw [update_frame_setLocal, hnext]; rfl, hsame₁⟩
    ⟨by simpa using hsum, rfl⟩

end SumTen

open SumTen in
/-- **sumTen** returns the sum of the values of the ten strings, and leaves the memory as it
was. -/
theorem sumTen_spec {lim : Limits} {P : Program} (hP : P[Proc.sumTen]? = some sumTenBody)
    (hLookup : LookupSpec lim P) (hs : Std lim) : SumTenSpec lim P := by
  intro x μ pre d hdep
  refine .of_body hP ?_
  rw [SumTenArgs.vals, ← pre.len]
  have hp := pre.star
  ((obtain ⟨⟩ := id hs); (obtain ⟨⟩ := id pre))
  have hsaved : μ (x.box + x.p) = (x.l[x.p] : ℕ) := pre.seg.getElem hp
  unfold tSumTen
  -- saved := mem[box + star]; sum := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.l[x.p] : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hsaved]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hsaved] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hsaved] <;> omega)));
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
          (0 : ℕ)
            -- for digit < 10
            
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
  -- for digit < 10
  refine Ends.next _ (Ends.for (Inv x x.l[x.p] μ) 10 (tRound x.l.length) ?start ?round ?done ?bound
    (hT := le_rfl)) (by simp [tRound]; omega)
  case start => exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl, .refl⟩
  case bound =>
    rintro j _ - - ⟨val, μ', rfl, -⟩
    simp
    omega
  case round =>
    rintro j _ hj - ⟨val, μ', rfl, hsame⟩
    exact round_spec hLookup hs pre hdep hj hsame
  case done =>
    rintro _ - ⟨val, μ', rfl, hsame⟩
    simp only [tRound]
    -- mem[box + star] := saved
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
          Light.Ends.storeToThen (x.box + x.p)
            (x.l[x.p] : ℕ)
              -- return sum
              
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
    -- return sum
    refine Ends.setTo _ ⟨by rw [List.take_of_length_le (by simp [tenValues])]; rfl,
      funext fun b => ?_⟩ ⟨by simp, rfl⟩
    dsimp only
    by_cases hb : b = x.box + x.p
    · rw [hb, Function.update_self, hsaved]
    · rw [Function.update_of_ne hb, hsame b hb]

end Light.Sec4

end
end

section


/-!
# The trie of one tile

Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile". Its proof: "We compute the values of the boxes in increasing
order of their number of stars." The routine takes a root for the trie of the tile and writes it
into the table of roots (Tile.Mem.newRoot). Then, for e = 0, …, m - t, it puts the boxes with e
stars into the trie (tileRound); for e ≥ 1 their values are sums of values looked up in the trie.
The invariant Tile.Inv says what the memory holds before the boxes with e stars; Tile.round takes it
from e to e + 1, and tile_spec is the root and the loop.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace Tile
















end Tile

















namespace Tile

/-! ## The pure side -/

/-- Behind the root and the boxes with fewer than e stars there is room for the boxes with e
stars. -/
theorem room (a b : List ℤ) (L m t root : ℕ) (T : List ℤ) {e : ℕ} (he : e ≤ m - t) :
    (fillUpTo a b L m t root e (trieNew T)).length + 11 * L * (starBoxes L m t e).length
      ≤ T.length + 11 * (1 + L * (boxes L m t).card) := by
  have hused := length_fillUpTo_le_sum a b L m t root e (trieNew T)
  rw [length_trieNew] at hused
  have hlists := List.sum_map_range_mono (fun e => (starBoxes L m t e).length)
    (show e + 1 ≤ m - t + 1 by omega)
  rw [sum_length_starBoxes, List.range_succ, List.map_append, List.sum_append] at hlists
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hlists
  have hmul := Nat.mul_le_mul_left (11 * L) hlists
  rw [Nat.mul_add] at hmul
  have hsplit : 11 * (1 + L * (boxes L m t).card) = 11 + 11 * L * (boxes L m t).card := by ring
  omega

/-- The time: the sum over the rounds, each with the test of the loop (6 steps). -/
theorem time_le (L m t n : ℕ) :
    ∑ i ∈ Finset.range n, (6 + (tFillList L (starBoxes L m t i).length + 30))
      ≤ ((List.range n).map fun e => tFillList L (starBoxes L m t e).length + 60).sum := by
  rw [List.sum_map_range]
  exact Finset.sum_le_sum fun _ _ => by omega

/-! ## The memory during the loop -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ₁ μ₂ : ℕ → ℤ} {x : TileArgs} {e : ℕ} {σ : State}
  {T T' : List ℤ}











/-- After the root of the tile has been taken and written behind the older roots. -/
theorem Mem.newRoot (C : TilePre lim μ x) (hs : SameOutsideTrie μ μ₁ x.tr x.cap x.fp)
    (ht : TrieMem μ₁ x.tr x.cap x.fp T) :
    Mem μ (Function.update μ₁ (x.aR + x.s.roots.length) (x.s.cells.length : ℤ)) x T := by
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  have hlayout := C.ctx.layout
  have hroots := C.rootsPlace
  exact
    { trie := ht.keep
      roots := SegN.snoc C.roots.keep _
      segA := C.segA.keep
      segB := C.segB.keep
      same := by ((try refine Light.SameOn.cell ?_);
                   (intro apspMacro_304924_0 apspMacro_304924_1);
                   (first
                     |
                       ((((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_304924_2));
                                   ((try
                                         have :=
                                           apspMacro_304924_2 apspMacro_304924_0 (by omega)));
                                   (revert apspMacro_304924_2)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (omega))
                     |
                       ((simp [] at apspMacro_304924_1);
                         (((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_304924_3));
                                   ((try
                                         have :=
                                           apspMacro_304924_3 apspMacro_304924_0 (by omega)));
                                   (revert apspMacro_304924_3)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (omega))
                     |
                       ((((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_304924_4));
                                   ((try
                                         have :=
                                           apspMacro_304924_4 apspMacro_304924_0 (by omega)));
                                   (revert apspMacro_304924_4)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (fail
                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                       its condition K x does not follow from the hypotheses.")))) }

/-- After the boxes with some number of stars have been put into the trie. -/
theorem Mem.fill (C : TilePre lim μ x) (h : Mem μ μ₁ x T)
    (hs : SameOutsideTile μ₁ μ₂ x.L x.tr x.cap x.fp x.cur x.box)
    (ht : TrieMem μ₂ x.tr x.cap x.fp T') : Mem μ μ₂ x T' := by
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hlenA := length_arrT x.encA
  have hlenB := length_arrT x.encB
  have hlayout := C.ctx.layout
  have hroots := C.rootsPlace
  have hsame := h.same
  exact { trie := ht, roots := h.roots.keep, segA := h.segA.keep, segB := h.segB.keep
          same := by ((try refine Light.SameOn.cell ?_);
                       (intro apspMacro_305535_0 apspMacro_305535_1);
                       (first
                         |
                           ((((repeat
                                     (((with_reducible
                                             rename Light.SameOn _ _ _ => apspMacro_305535_2));
                                       ((try
                                             have :=
                                               apspMacro_305535_2 apspMacro_305535_0 (by omega)));
                                       (revert apspMacro_305535_2)));
                                 (intros);
                                 (try simp only [Function.update_apply, Light.wrote] at *)));
                             (omega))
                         |
                           ((simp [] at apspMacro_305535_1);
                             (((repeat
                                     (((with_reducible
                                             rename Light.SameOn _ _ _ => apspMacro_305535_3));
                                       ((try
                                             have :=
                                               apspMacro_305535_3 apspMacro_305535_0 (by omega)));
                                       (revert apspMacro_305535_3)));
                                 (intros);
                                 (try simp only [Function.update_apply, Light.wrote] at *)));
                             (omega))
                         |
                           ((((repeat
                                     (((with_reducible
                                             rename Light.SameOn _ _ _ => apspMacro_305535_4));
                                       ((try
                                             have :=
                                               apspMacro_305535_4 apspMacro_305535_0 (by omega)));
                                       (revert apspMacro_305535_4)));
                                 (intros);
                                 (try simp only [Function.update_apply, Light.wrote] at *)));
                             (fail
                                 "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                           SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                           its condition K x does not follow from the hypotheses.")))) }

/-! ## The invariant and one round -/


















/-- One round puts the boxes with e stars into the trie. -/
theorem round (hFill : FillListSpec lim P) (C : TilePre lim μ x) (hd : d + 3 ≤ lim.depth)
    (he : e ≤ x.m - x.t) (h : Inv μ x e σ) :
    Ends lim P d tileRound σ (tFillList x.L (starBoxes x.L x.m x.t e).length + 30)
      (Inv μ x (e + 1)) := by
  obtain ⟨void, μ₁, rfl, hM⟩ := h
  have hlayout := C.ctx.layout
  ((obtain ⟨⟩ := id C.ctx); (obtain ⟨⟩ := id C.ctx.std))
  -- the trie of the tile has the number s.roots.length, and its root is the last one
  have hroot := x.s.root_new
  have hfill := hFill (fillArgs x e) μ₁
    { ctx := C.ctx, stars_le := he, root_ne := hroot.trans_ne C.rep.length_pos.ne'
      rep := fillUpTo_rep (arrT x.encA) (arrT x.encB) x.m x.t x.s C.rep e
      trie := hM.trie, segA := hM.segA, segB := hM.segB
      room := (room (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length x.s.cells he).trans
        C.room }
  simp only [fillArgs, FillListArgs.vals, FillListArgs.root, FillListArgs.boxes, hroot] at hfill
  -- fillList(e, root, …)
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
          Light.Ends.callToThen ((hfill _ (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (hfill _ (by omega)) ?_ ?_ ?_ ?_);
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
        ((rintro void' μ₂
              ⟨htrie, same⟩
                  -- e := e + 1
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- e := e + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (e + 1 : ℕ) ?_ ?_ ?_);
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
  exact ⟨void', μ₂, rfl, hM.fill C same htrie⟩

end Tile

open Tile in
/-- **tile** meets its specification. -/
theorem tile_spec {lim : Limits} {P : Program} (hP : P[Proc.tile]? = some tileBody)
    (hNew : NewRootSpec lim P) (hFill : FillListSpec lim P) : TileSpec lim P := by
  intro x μ C
  refine fun d hd => ⟨tileBody, hP, ?_⟩
  have hlayout := C.ctx.layout
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.ctx); (obtain ⟨⟩ := id C.ctx.std))
  have hcells : x.cells = x.s.roots.length + 1 := rfl
  have hroom := C.room
  unfold tTile
  -- root := newRoot(tr, fp)
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
            ((hNew x.tr x.cap x.fp x.s.cells μ C.trie (by omega) (by omega)
                (by omega) _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hNew x.tr x.cap x.fp x.s.cells μ C.trie (by omega) (by omega)
              (by omega) _ (by omega))
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
        ((rintro _ μ₁
              ⟨rfl, htrie, same⟩
                  -- mem[ra] := root
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- mem[ra] := root
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
        Light.Ends.storeToThen (x.aR + x.s.roots.length) x.s.cells.length ?_ ?_
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
  -- while e ≤ mt
  refine (Ends.while (Inv μ x) (x.m - x.t + 1)
    (fun e => tFillList x.L (starBoxes x.L x.m x.t e).length + 30)
    ?start ?round ?done).mono ?time fun _ h => h
  case start => exact ⟨0, _, congrArg (State.mk · _) (frame_append_zeros _ 1).symm,
    Mem.newRoot C same htrie⟩
  case round =>
    rintro e σ he hI
    have hround := round hFill C hd (by omega) hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, hround⟩
  case done =>
    rintro _ ⟨void, μ', rfl, hM'⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp, hM'.trie, hM'.roots, hM'.same⟩
  case time =>
    have hsum := time_le x.L x.m x.t (x.m - x.t + 1)
    -- the test of the loop and the jump cost 6 steps
    have htest : ∀ y : ℕ, 1 + (1 + 1 + 1) + 1 + 1 + y = 6 + y := fun y => by omega
    simp only [Cond.cost, Expr.cost, htest]
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
          | ((ring_nf); (omega)))

end Light.Sec4

end
end

section


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4



























/-- **Every program that holds the routines of Section 4 at their numbers meets all their
specifications.** -/
theorem specs40_sourceProof {lim : Limits} {P : Program} (h : Has40 P) (hs : Std lim) : Specs40 lim P := by
  have nineFirst : NineFirstSpec lim P := nineFirst_spec (h 0 (by omega)) hs
  have nineNext : NineNextSpec lim P := nineNext_spec (h 1 (by omega)) hs
  have scatter : ScatterSpec lim P := scatter_spec (h 2 (by omega)) hs
  have starFirst : StarFirstSpec lim P := starFirst_spec (h 3 (by omega)) hs
  have horner : HornerSpec lim P := horner_spec (h 4 (by omega)) hs
  have lookup : LookupSpec lim P := lookup_spec (h 5 (by omega)) hs
  have insert : InsertSpec lim P := insert_spec (h 6 (by omega)) hs
  have newRoot : NewRootSpec lim P := newRoot_spec (h 7 (by omega)) hs
  have sumTen : SumTenSpec lim P := sumTen_spec (h 8 (by omega)) lookup hs
  have fillList : FillListSpec lim P := fillList_spec
    (h 9 (by omega)) nineFirst nineNext starFirst horner insert sumTen
  have tile : TileSpec lim P := tile_spec (h 10 (by omega)) newRoot fillList
  have allTiles : AllTilesSpec lim P := allTiles_spec (h 11 (by omega)) tile
  have outDigits : OutDigitsSpec lim P := outDigits_spec (h 12 (by omega))
  have queryCore : QueryCoreSpec lim P :=
    queryCore_spec (h 13 (by omega)) ⟨nineFirst, nineNext, scatter, horner, lookup⟩
  exact ⟨nineFirst, nineNext, scatter, starFirst, horner, lookup, insert, newRoot, sumTen,
    fillList, tile, allTiles,
    outDigits, queryCore⟩































end Light.Sec4

end
end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}, Light.Sec4.Has40 P → Light.Std lim → Light.Sec4.Specs40 lim P := by
  exact @Light.Sec4.specs40_sourceProof

#print axioms solution
