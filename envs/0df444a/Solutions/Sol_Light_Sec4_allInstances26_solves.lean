-- Prove2me | solution 1 for Light.Sec4.allInstances26_solves
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:35:16.498093+00:00
-- url     : https://prove2.me/submissions/338b07e2-c06b-4ffa-9c32-fb74f59cc26b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_ParameterSteps
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Theorem30
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
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
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
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
import Theorems.Thm_ThreeSumApsp_Corollary26_le_K
import Theorems.Thm_ThreeSumApsp_Corollary26_threshold
import Theorems.Thm_ThreeSumApsp_sum_alpha_le

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

/-- Loops whose number of rounds depends on the data.  I is the invariant, m a quantity that every
round decreases, and b bounds the cost of a round. -/
theorem Ends.whileVariant {σ c s T} {Q : State → Prop} (I : State → Prop) (m : State → ℕ) (b : ℕ)
    (hI : I σ) (hsafe : ∀ σ, I σ → c.Safe lim σ)
    (hs : ∀ σ, I σ → c.Holds σ → Ends lim P d s σ b fun σ' => I σ' ∧ m σ' < m σ)
    (hn : ∀ σ, I σ → ¬ c.Holds σ → Q σ) (hT : m σ * (c.cost + 1 + b) + (c.cost + 1) ≤ T) :
    Ends lim P d (.while c s) σ T Q := by
  have key : ∀ n σ, I σ → m σ ≤ n →
      Ends lim P d (.while c s) σ (m σ * (c.cost + 1 + b) + (c.cost + 1)) Q := by
    intro n
    induction n with
    | zero =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, -, -, -, hlt⟩ := hs σ h hc
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
    | succ n ih =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, he₁, hk₁, hI₁, hlt⟩ := hs σ h hc
        obtain ⟨σ₂, k₂, he₂, hk₂, hq⟩ := ih σ₁ hI₁ (by omega)
        refine ⟨σ₂, _, .whileTrue (hsafe _ h) hc he₁ he₂, ?_, hq⟩
        have h1 : (m σ₁ + 1) * (c.cost + 1 + b) ≤ m σ * (c.cost + 1 + b) :=
          Nat.mul_le_mul_right _ hlt
        have h2 : (m σ₁ + 1) * (c.cost + 1 + b) = m σ₁ * (c.cost + 1 + b) + (c.cost + 1 + b) := by
          ring
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
  exact (key _ σ hI le_rfl).mono hT fun _ h => h

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





















/-- An assignment, followed by the rest of the program. -/
theorem Ends.setThen {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩ (T - (e.cost + 1)) Q)
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
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.set hs le_rfl h) hT

















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




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl


















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























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl



































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





























theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl






/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc









/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)












































































end Light

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











































/-! ### The order of a leaf -/









































/-! ### The counts -/































































/-- Section 2.4.3: "In particular, β₀ = binom(L, m) 9^{L-m}". -/
theorem beta_zero (L m : ℕ) : beta L m 0 = L.choose m * 9 ^ (L - m) := by
  simp [beta]

/-- Section 2.4.3: "β₀ = binom(L, m) 9^{L-m} = M". -/
theorem beta_zero_eq_M (L m : ℕ) : beta L m 0 = M L m := by
  rw [beta_zero, M, K, N0, ← pow_mul, mul_comm (L - m) 2, pow_mul]
  norm_num




















































































































end ThreeSumApsp

end
end

section


/-!
# Binomial coefficients

Upper bounds. A single summand of the binomial expansion of `(a + b) ^ n` is at most the whole sum
(`Nat.choose_mul_pow_mul_pow_le`); with `a = 1` this is `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`
(`Nat.choose_mul_pow_le`), which the paper uses with `b = 9`. And `binom(n, k) ≤ (e n / k) ^ k`
(`Nat.choose_le_exp_mul_div_pow`).

A lower bound. For `k ≤ n`, the largest of the `n + 1` terms `binom(n, j) k^j (n-k)^{n-j}` of the
expansion of `n^n = (k + (n-k))^n` is the one with `j = k`: the terms increase up to `j = k` and
decrease from there on. This gives the standard lower bound on a binomial coefficient
(`Nat.pow_self_le_mul_choose_mul_pow_mul_pow`), which Section 4.4 uses in the proof of Corollary 26
and, written with the entropy function as `e^{n H(k/n)}/(n+1) ≤ binom(n, k)`, in the proof of
Corollary 31.
-/

public section

namespace Nat

/-! ## Upper bounds -/

/-- One summand of the binomial expansion of `(a + b) ^ n` is at most `(a + b) ^ n`. -/
theorem choose_mul_pow_mul_pow_le (a b n k : ℕ) :
    n.choose k * a ^ k * b ^ (n - k) ≤ (a + b) ^ n := by
  obtain hk | hk := le_or_gt k n
  · rw [add_pow]
    calc n.choose k * a ^ k * b ^ (n - k) = a ^ k * b ^ (n - k) * n.choose k := by ring
      _ ≤ _ := Finset.single_le_sum (f := fun k => a ^ k * b ^ (n - k) * n.choose k)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt hk, zero_mul, zero_mul]
    exact Nat.zero_le _

/-- `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`. -/
theorem choose_mul_pow_le (b n k : ℕ) : n.choose k * b ^ (n - k) ≤ (b + 1) ^ n := by
  simpa only [one_pow, mul_one, add_comm] using choose_mul_pow_mul_pow_le 1 b n k


















/-! ## The largest term of a binomial expansion -/
























































end Nat

end
end

section


/-!
# Theorem 5: an instance of the task, in the terms of Section 2

An instance of the thin matrix product is given by lists in the memory. This file reads them as the
matrices X and Y and the set W of Section 2, and has the facts that link the two descriptions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp






































variable {x : ThinInst} {m : ℕ} {μ : ℕ → ℤ} {fr : ℕ}































section positions

variable {i : ℕ}

/-- A number of a wanted position is an index of the list of the rows. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWI (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WI.length :=
  hi.trans_eq hpre.lenWI.symm

/-- A number of a wanted position is an index of the list of the columns. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWJ (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WJ.length :=
  hi.trans_eq hpre.lenWJ.symm

/-- A number of a wanted position is an index of the list of the positions. -/
theorem _root_.Light.ThinInst.Pre.lt_lenZip (hpre : x.Pre μ fr) (hi : i < x.w) :
    i < (x.WI.zip x.WJ).length := by
  simp [hpre.lenWI, hpre.lenWJ, hi]

theorem thinI_eq (h : i < x.WI.length) : thinI x i = x.WI[i] := List.getD_eq_getElem _ _ h

theorem thinJ_eq (h : i < x.WJ.length) : thinJ x i = x.WJ[i] := List.getD_eq_getElem _ _ h

/-- The rows of the wanted positions are rows of the matrix. -/
theorem thinI_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinI x i < x.N := by
  rw [thinI_eq (hpre.lt_lenWI hi)]
  exact hpre.ltWI _ (List.getElem_mem _)

/-- The columns of the wanted positions are columns of the matrix. -/
theorem thinJ_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinJ x i < x.N := by
  rw [thinJ_eq (hpre.lt_lenWJ hi)]
  exact hpre.ltWJ _ (List.getElem_mem _)

/-- The rows of the wanted positions, in the memory. -/
theorem mem_thinI (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wi + i) = (thinI x i : ℕ) := by
  rw [thinI_eq (hpre.lt_lenWI hi), hpre.segWI i (by simpa using hpre.lt_lenWI hi),
    List.getElem_map]

/-- The columns of the wanted positions, in the memory. -/
theorem mem_thinJ (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wj + i) = (thinJ x i : ℕ) := by
  rw [thinJ_eq (hpre.lt_lenWJ hi), hpre.segWJ i (by simpa using hpre.lt_lenWJ hi),
    List.getElem_map]

end positions































/-- There is one answer for each wanted position. -/
theorem length_thinOut (hpre : x.Pre μ fr) : (thinOut x.N x.D x.X x.Y x.WI x.WJ).length = x.w := by
  simp [thinOut, hpre.lenWI, hpre.lenWJ]

/-- The answer number i. -/
theorem getD_thinOut (hpre : x.Pre μ fr) {i : ℕ} (hi : i < x.w) :
    (thinOut x.N x.D x.X x.Y x.WI x.WJ).getD i 0
      = thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) := by
  rw [thinI_eq (hpre.lt_lenWI hi), thinJ_eq (hpre.lt_lenWJ hi)]
  unfold thinOut
  rw [List.getD_eq_getElem _ _ (by simpa using hpre.lt_lenZip hi), List.getElem_map,
    List.getElem_zip]

end Light.Sec2

end
end

section


/-!
# The wanted entries of a thin matrix product, as inner products

X is an N × D matrix at the address x and Y a D × N matrix at y, both row by row, with entries of
absolute value at most U; the cells from wi and from wj on hold the rows and the columns of w wanted
positions.  thinBrute(N, D, w, U, x, y, wi, wj, out, fr) computes every wanted entry (XY)[I, J] as
the inner product of row I of X and column J of Y, and writes it to the cells from out on.  It is
right on every instance for which D U² fits in a word, so that no partial sum overflows; it is what
the solver of Theorem 5 falls back to outside the regime of the theorem.  At most
40 (w + 1) (D + 1) steps.

bruteInner_spec treats the inner product: after t rounds the sum holds the first t terms
(brutePartial), which stay within a word (abs_brutePartial_le).  bruteRound_spec treats one wanted
position, and thinBrute_spec the loop over the positions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute












end Brute

open ThinArg Brute






























/-! ## The partial sums -/





/-- One more term. -/
theorem brutePartial_succ (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) :
    brutePartial N D X Y I J (n + 1)
      = brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0 := by
  simp [brutePartial, List.range_succ]

/-- A term of the inner product is at most U². -/
theorem abs_bruteTerm_le {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U) (a b : ℕ) :
    |X.getD a 0 * Y.getD b 0| ≤ (U * U : ℕ) := by
  rw [abs_mul]
  push_cast
  exact mul_le_mul (hX.abs_getD_le (by positivity) a) (hY.abs_getD_le (by positivity) b)
    (abs_nonneg _) (by positivity)

/-- The first n terms add up to at most n U². -/
theorem abs_brutePartial_le {N D : ℕ} {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (I J n : ℕ) : |brutePartial N D X Y I J n| ≤ n * (U * U : ℕ) := by
  induction n with
  | zero => simp [brutePartial]
  | succ n ih =>
    rw [brutePartial_succ]
    calc |brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0|
        ≤ |brutePartial N D X Y I J n| + |X.getD (I * D + n) 0 * Y.getD (n * N + J) 0| :=
          abs_add_le _ _
      _ ≤ n * (U * U : ℕ) + (U * U : ℕ) := add_le_add ih (abs_bruteTerm_le hX hY _ _)
      _ = ((n + 1 : ℕ) : ℤ) * (U * U : ℕ) := by push_cast; ring

/-! ## The program -/

/-- **The inner product** of row I of X and column J of Y. -/
theorem bruteInner_spec (std : Std lim) (x : ThinInst) {μ : ℕ → ℤ} {fr i I J : ℕ} {u : ℤ}
    (segX : Seg μ x.x x.X) (segY : Seg μ x.y x.Y) (lX : x.X.length = x.N * x.D)
    (lY : x.Y.length = x.D * x.N) (bX : AbsLe x.X x.U) (bY : AbsLe x.Y x.U) (hI : I < x.N)
    (hJ : J < x.N) (roomX : x.x + x.N * x.D < lim.space) (roomY : x.y + x.D * x.N + x.N < lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d bruteInner ⟨frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩
      (24 * x.D + 4) fun σ' => σ' = ⟨frame (bruteLocs x u fr i x.D (x.x + I * x.D + x.D)
        (x.y + x.D * x.N + J) (brutePartial x.N x.D x.X x.Y I J x.D)), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  unfold bruteInner
  refine Ends.whileBlock (fun t σ => σ = ⟨frame (bruteLocs x u fr i t (x.x + I * x.D + t)
    (x.y + t * x.N + J) (brutePartial x.N x.D x.X x.Y I J t)), μ⟩) x.D
    (by simp [brutePartial]) ?round ?done
  case round =>
    rintro t _ ht rfl
    have htN := Nat.mul_add_le_mul ht (le_refl x.N)
    have rX : μ (x.x + I * x.D + t) = x.X.getD (I * x.D + t) 0 := by
      rw [Nat.add_assoc]
      exact segX.getD (by omega) 0
    have rY : μ (x.y + t * x.N + J) = x.Y.getD (t * x.N + J) 0 := by
      rw [Nat.add_assoc]
      exact segY.getD (by omega) 0
    have hmono : ∀ n ≤ x.D, ((n : ℤ) * (x.U * x.U : ℕ)) ≤ lim.word := fun n hn =>
      le_trans (by exact_mod_cast Nat.mul_le_mul_right (x.U * x.U) hn) hword
    have hsum := abs_le.mp ((abs_brutePartial_le (N := x.N) (D := x.D) bX bY I J (t + 1)).trans
      (by exact_mod_cast hmono (t + 1) (by omega)))
    have hterm := abs_le.mp ((abs_bruteTerm_le bX bY (I * x.D + t) (t * x.N + J)).trans
      (by simpa using hmono 1 (by omega)))
    have hnext := brutePartial_succ x.N x.D x.X x.Y I J t
    rw [hnext] at hsum
    generalize x.X.getD (I * x.D + t) 0 = a, x.Y.getD (t * x.N + J) 0 = b at *
    generalize hpx : x.x + I * x.D + t = px at *
    generalize hpy : x.y + t * x.N + J = py at *
    have hpx' : (px : ℤ) + 1 = x.x + I * x.D + (t + 1) := by rw [← hpx]; push_cast; ring
    have hpy' : (py : ℤ) + x.N = x.y + (t + 1) * x.N + J := by rw [← hpy]; push_cast; ring
    exact ⟨by simp, by simp [bruteLocs]; omega,
      by (((try have := Light.Std.space_le (by assumption)));
           ((try have := Light.Std.const_le (by assumption)));
           (simp [Light.Limits.Addr, abs_le, -abs_mul, bruteLocs, rX, rY] <;> omega)),
      by simp [bruteLocs, update_frame_setLocal, rX, rY, hnext, hpx', hpy']⟩
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [bruteLocs], rfl⟩








/-- **One wanted position.** -/
theorem bruteRound_spec (std : Std lim) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} {u : ℤ}
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < x.w) {σ : State}
    (h : BruteInv x μ u fr i σ) :
    Ends lim P d bruteRound σ (24 * x.D + 33) (BruteInv x μ u fr (i + 1)) := by
  obtain ⟨t, px, py, s, μ', rfl, hdone, hfr⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hbelow := And.intro hpre.belowX (And.intro hpre.belowY (And.intro hpre.belowWI
    (And.intro hpre.belowWJ hpre.belowOut)))
  have hI := thinI_lt hpre hi
  have hJ := thinJ_lt hpre hi
  have segX : Seg μ' x.x x.X :=
    hpre.segX.of_sameOutside hfr (by rw [hpre.lenX]; exact hpre.apartX.symm)
  have segY : Seg μ' x.y x.Y :=
    hpre.segY.of_sameOutside hfr (by rw [hpre.lenY]; exact hpre.apartY.symm)
  have rI : μ' (x.wi + i) = (thinI x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWI with h | h <;> omega)]
    exact mem_thinI hpre hi
  have rJ : μ' (x.wj + i) = (thinJ x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWJ with h | h <;> omega)]
    exact mem_thinJ hpre hi
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  have hND : x.N ≤ x.D * x.N := Nat.le_mul_of_pos_left _ hpre.D_pos
  unfold bruteRound bruteLocs
  -- t := 0; px := x + mem[wi + i] * D; py := y + mem[wj + i]; s := 0
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
    (refine Light.Ends.setToThen (x.x + thinI x i * x.D : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rI]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [rI] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, rI] <;> omega)));
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
    (refine Light.Ends.setToThen (x.y + thinJ x i : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rJ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [rJ] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, rJ] <;> omega)));
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
            -- the inner product
            
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
  -- the inner product
  refine Ends.next (24 * x.D + 4) ((bruteInner_spec std x (i := i) segX segY hpre.lenX hpre.lenY
    hpre.leX hpre.leY hI hJ (by omega) (by omega) hword).mono le_rfl ?_)
  rintro _ rfl
  unfold bruteLocs
  -- mem[out + i] := s; i := i + 1
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
        Light.Ends.storeToThen (x.out + i)
          (brutePartial x.N x.D x.X x.Y (thinI x i) (thinJ x i) x.D) ?_ ?_ ?_);
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
  refine ⟨_, _, _, _, _, rfl, fun j hj => ?_,
    hfr.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · rw [Function.update_of_ne (by omega)]
    exact hdone j hlt
  · rw [Function.update_self]
    rfl

/-- **The brute force is right on every instance** for which D U² fits in a word.  It needs N + 1
cells above the free pointer only as room for addresses that are formed and never used. -/
theorem thinBrute_spec (std : Std lim) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (u : ℤ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d thinBruteBody
      ⟨frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ),
        (x.out : ℤ), (fr : ℤ)], μ⟩
      (40 * ((x.w + 1) * (x.D + 1))) fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  unfold thinBruteBody
  refine Ends.whileConst (BruteInv x μ u fr) x.w (24 * x.D + 33) ?start ?round ?done ?time
  case start =>
    exact ⟨0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, fun j hj => absurd hj (by omega),
      SameOutside.refl⟩
  case round =>
    intro i σ hi h
    refine ⟨?_, ?_, bruteRound_spec std hpre hsp hword hi h⟩ <;>
      obtain ⟨t, px, py, s, μ', rfl, -, -⟩ := h
    · simp
    · simpa [bruteLocs] using hi
  case done =>
    rintro _ ⟨t, px, py, s, μ', rfl, hdone, hfr⟩
    refine ⟨by simp, by simp [bruteLocs], fun i hi => ?_, fun a ha => hfr a ha.2⟩
    have hi' : i < x.w := by rwa [length_thinOut hpre] at hi
    change μ' (x.out + i) = _
    rw [hdone i hi', ← getD_thinOut hpre hi', List.getD_eq_getElem _ _ hi]
  case time =>
    have hleft : x.w * (4 + (24 * x.D + 33)) = 24 * (x.w * x.D) + 37 * x.w := by ring
    have hright : (x.w + 1) * (x.D + 1) = x.w * x.D + x.w + x.D + 1 := by ring
    simp
    omega

end Light.Sec2

end
end

section


/-!
# The regime of Theorem 5

"Let D ≥ 4 be a power of four and N ≥ D^18 … a set W of at most N²/√D positions".  The procedure
regime(N, D, w), where w is the number of positions in W, tests whether the sizes of an instance are
in this regime.  It returns the exponent m with D = 4^m if they are, and 0 if they are not.  With
√D = 2^m, the condition on W reads w 2^m ≤ N².

The program has these parts, each with its own lemma.  regimeExp multiplies by four until D is
reached, which gives the only candidate m = ⌈log₄ D⌉ together with 4^m and 2^m = √D.  regimePow
compares D^18 with N by at most eighteen multiplications, none of which exceeds N D (but for the
first product, which is D).  regimeTests combines the four tests, the last two of which are
regimeSizes.  That the candidate is the only one is RegimeAnswer.zero.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}












/-! ## The local variables -/

namespace RegimeLocal






















end RegimeLocal

open RegimeLocal

/-! ## The text -/















































/-! ## What the procedure returns -/










/-! ## The exponent -/


























/-! ## The eighteenth power -/











/-- A round of regimePow keeps PowInv and brings local 8 closer to 18. -/
theorem regimePowRound_spec {N D : ℕ} (hD : 1 ≤ D)
    (hword : (4 * D + N * D + 100 : ℤ) ≤ lim.word) {μ loc : ℕ → ℤ} (e0 : loc 0 = N)
    (e1 : loc 1 = D) {σ : State} (hinv : PowInv N D loc μ σ) (htest : ((Light.Cond.lt (v 8) (k 18))).Holds σ) :
    Ends lim P d regimePowRound σ 14 fun σ' =>
      PowInv N D loc μ σ' ∧ 18 - (σ'.loc 8).toNat < 18 - (σ.loc 8).toNat := by
  unfold regimePowRound Rows Cols Power Count Fits
  obtain ⟨loc', μ'⟩ := σ
  obtain ⟨hmem, hkept, hcase⟩ := hinv
  dsimp only at hmem hkept hcase
  subst hmem
  have hN := (hkept 0 (by omega)).trans e0
  have hDloc := (hkept 1 (by omega)).trans e1
  obtain ⟨j, -, hexp, hok, hpow, hle⟩ | ⟨hexp, -, -⟩ := hcase
  swap
  · simp [hexp] at htest
  have hj : j < 18 := by simpa [hexp] using htest
  have hnext : D ^ j * D ≤ 4 * D + N * D := by
    rcases hle with rfl | hle
    · simp
      omega
    · exact (Nat.mul_le_mul_right D hle).trans (Nat.le_add_left _ _)
  have hsucc : D ^ (j + 1) = D ^ j * D := pow_succ D j
  have hmono : D ^ (j + 1) ≤ D ^ 18 := Nat.pow_le_pow_right hD hj
  generalize D ^ j = q at *
  have hnextZ : (q : ℤ) * D ≤ 4 * D + N * D := by exact_mod_cast hnext
  have hq0 : (0 : ℤ) ≤ (q : ℤ) * D := by positivity
  have hsafe : ((Light.Cond.lt (v 0) ((Light.Expr.op Light.Op.mul) (v 7) (v 1)))).Safe lim ⟨loc', μ'⟩ := by
    simp [hpow, hDloc, abs_le, -abs_mul]
    omega
  by_cases hlt : N < q * D
  · -- ok := 0; j := 18
    have hltZ : (N : ℤ) < q * D := by exact_mod_cast hlt
    refine Ends.block (.ite_pos ⟨by simp; omega, ⟨rfl, fun x hx => ?_,
      Or.inr ⟨by simp, by simp, by omega⟩⟩, by simp [hexp]; omega⟩
      (by simp [hN, hpow, hDloc]; omega) hsafe)
    simp only [Stmt.after, Function.update_apply]
    split_ifs <;> first | omega | exact hkept x hx
  · -- q := q D; j := j + 1
    have hgeZ : (q : ℤ) * D ≤ N := by exact_mod_cast not_lt.1 hlt
    refine Ends.block (.ite_neg ⟨by (((try have := Light.Std.space_le (by assumption)));
                                        ((try have := Light.Std.const_le (by assumption)));
                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, hpow, hDloc, hexp] <;> omega)),
      ⟨rfl, fun x hx => ?_, Or.inl ⟨j + 1, hj, by simp [hexp], by simp [hok],
        by simp [hpow, hDloc, hsucc], Or.inr (by omega)⟩⟩, by simp [hexp]; omega⟩
      (by simp [hN, hpow, hDloc]; omega) hsafe)
    simp only [Stmt.after, Function.update_apply]
    split_ifs <;> first | omega | exact hkept x hx

/-- regimePow leaves the memory and the locals below 7 as they are.  Afterwards local 9 is 1 if
D^18 ≤ N and 0 if not. -/
theorem regimePow_spec (N D : ℕ) (hD : 1 ≤ D)
    (hword : ((4 * D + N * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) (loc : ℕ → ℤ)
    (e0 : loc 0 = N) (e1 : loc 1 = D) :
    Ends lim P d regimePow ⟨loc, μ⟩ 334 fun σ' =>
      σ'.mem = μ ∧ (∀ x < 7, σ'.loc x = loc x) ∧
        ((σ'.loc 9 = 1 ∧ D ^ 18 ≤ N) ∨ (σ'.loc 9 = 0 ∧ N < D ^ 18)) := by
  push_cast at hword
  have hND : (0 : ℤ) ≤ (N : ℤ) * D := by positivity
  unfold regimePow Power Count Fits
  -- q := 1; j := 0; ok := 1
  refine Ends.setThen (Ends.setThen (Ends.setThen ?_))
  -- while j < 18: one round
  refine Ends.whileVariant (PowInv N D loc μ) (fun σ => 18 - (σ.loc 8).toNat) 14
    ?start ?safe (fun σ => regimePowRound_spec hD hword e0 e1) ?done (by simp)
  case start =>
    refine ⟨rfl, fun x hx => ?_, Or.inl ⟨0, by omega, by simp, by simp, by simp, Or.inl rfl⟩⟩
    simp only [Function.update_apply]
    split_ifs <;> omega
  case safe =>
    rintro σ -
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
  case done =>
    rintro ⟨loc', μ'⟩ ⟨hmem, hkept, hcase⟩ htest
    dsimp only at hmem hkept hcase
    obtain ⟨j, hj, hexp, hok, -, hle⟩ | ⟨-, hok, hlt⟩ := hcase
    · obtain rfl : j = 18 := by
        have : ¬ j < 18 := by simpa [hexp] using htest
        omega
      exact ⟨hmem, hkept, Or.inl ⟨hok, by omega⟩⟩
    · exact ⟨hmem, hkept, Or.inr ⟨hok, hlt⟩⟩

/-! ## The four tests -/














































































/-! ## The whole procedure -/




























end Light.Sec2

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

/-- Section 4, "Notions from Section 2": "we will use that M = β₀ ≤ 10^L". The equation is
`beta_zero_eq_M`; this is the inequality. -/
theorem M_le_ten_pow (L m : ℕ) : M L m ≤ 10 ^ L := by
  -- `binom(L, m) 9^{L-m}` is one summand of the binomial expansion of `(9 + 1)^L`
  rw [← beta_zero_eq_M, beta_zero]
  exact Nat.choose_mul_pow_le 9 L m

/-! ### Cubes and their leaves (Section 4.2) -/

























































/-! ### A leaf as a cube without stars (Section 4.2) -/
























/-! ### Replacing a star by a term (proof of Lemma 29) -/
































/-! ### Putting stars into a leaf (Section 4.2) -/




































/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/




























/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/






































/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/


























/-! ### The `k` lowest levels of a set (Section 4.2) -/



































































/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/










































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








/-- The decay rate `ρ` is not negative when `L ≥ 10m`. -/
theorem rho_nonneg {L m : ℕ} (hL : 10 * m ≤ L) : 0 ≤ rho L m := by
  have hL' : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact div_nonneg (by positivity) (by linarith)







































/-! ### Theorem 30, "Preprocessing": the count behind (8) -/




/-- `√K N₀` is positive when `m ≤ L`. -/
theorem sqrtKN0_pos {L m : ℕ} (hmL : m ≤ L) : 0 < sqrtKN0 L m := by
  have hK : (0 : ℝ) < (K L m : ℝ) := by exact_mod_cast Nat.choose_pos hmL
  have hN0 : (0 : ℝ) < (N0 L m : ℝ) := by exact_mod_cast N0_pos L m
  exact mul_pos (Real.sqrt_pos.mpr hK) hN0

/-- `(√K N₀)² = K N₀² = M`. -/
theorem sqrtKN0_sq (L m : ℕ) : sqrtKN0 L m ^ 2 = (M L m : ℝ) := by
  rw [sqrtKN0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp [M]






























/-- Proof of Theorem 30, "Preprocessing": "we store the K₀² subsets, in O(KL) ≤ O(10^L) operations".
Read as the inequality `K L ≤ 10^L` (constant 1). -/
theorem Theorem30.subsets (L m : ℕ) : K L m * L ≤ 10 ^ L := by
  calc K L m * L ≤ 2 ^ L * 2 ^ L :=
        Nat.mul_le_mul (Nat.choose_le_two_pow L m) Nat.lt_two_pow_self.le
    _ = 4 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 10 ^ L := Nat.pow_le_pow_left (by norm_num) L





























































/-- Proof of Theorem 30, "Preprocessing": "K N₀ D ≤ 7^L". This bounds the number of nonzero entries
of the input array of a band, which is why forming it takes `O(L · 7^L)` operations. -/
theorem Theorem30.K_mul_N0_mul_D_le (L m : ℕ) : K L m * N0 L m * D m ≤ 7 ^ L := by
  -- one summand of the binomial expansion of `(4 + 3)^L`
  calc K L m * N0 L m * D m = L.choose m * 4 ^ m * 3 ^ (L - m) := by unfold K N0 D; ring
    _ ≤ 7 ^ L := Nat.choose_mul_pow_mul_pow_le 4 3 L m

/-- Proof of Theorem 30, "Preprocessing": forming the input array of a band takes "O(L · 7^L)
operations", which is within the "O(10^L) operations" of its encoding ("This is the last term of
(8)"). Read as the inequality `L · 7^L ≤ 2 · 10^L`; the constant 1 fails at `L = 3`. From `L = 3`
on, one more level multiplies the left-hand side by `7(L+1)/L ≤ 10`. -/
theorem Theorem30.form_array : ∀ L : ℕ, L * 7 ^ L ≤ 2 * 10 ^ L
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | L + 4 =>
    calc (L + 4) * 7 ^ (L + 4) = (7 * (L + 4)) * 7 ^ (L + 3) := by ring
      _ ≤ (10 * (L + 3)) * 7 ^ (L + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 * ((L + 3) * 7 ^ (L + 3)) := by ring
      _ ≤ 10 * (2 * 10 ^ (L + 3)) := Nat.mul_le_mul_left _ (Theorem30.form_array (L + 3))
      _ = 2 * 10 ^ (L + 4) := by ring




































































































/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/






























































/-! ### Theorem 30, "Word size" -/

/-- Proof of Theorem 30, "Word size": "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}".
Stated after squaring, to stay in the natural numbers. -/
theorem Theorem30.ten_pow_le (L m N : ℕ) (hL : 10 * m ≤ L) (hN : N0 L m ≤ N) :
    (10 ^ L) ^ 2 ≤ N ^ 5 := by
  -- squared once more: `10^{4L} ≤ 3^{9L} ≤ 3^{10(L-m)}`
  have hsq : ((10 ^ L) ^ 2) ^ 2 ≤ ((3 ^ (L - m)) ^ 5) ^ 2 :=
    calc ((10 ^ L) ^ 2) ^ 2 = 10000 ^ L := by
          rw [← pow_mul, ← pow_mul, mul_comm L, pow_mul]; norm_num
      _ ≤ 19683 ^ L := Nat.pow_le_pow_left (by norm_num) L
      _ = 3 ^ (9 * L) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ ((L - m) * 5 * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = ((3 ^ (L - m)) ^ 5) ^ 2 := by rw [pow_mul, pow_mul]
  exact ((Nat.pow_le_pow_iff_left (by norm_num)).mp hsq).trans (Nat.pow_le_pow_left hN 5)

end ThreeSumApsp

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

/-- The directory lies before the areas of Section 4. -/
theorem wd_ge (p : Sec2.Par) (b0 : ℕ) : b0 + 32 ≤ aWD p b0 := by
  obtain ⟨⟩ := areas p 0 b0
  omega

/-- The shared block ends behind its base address. -/
theorem base_le_sharedEnd (p : Sec2.Par) (b0 : ℕ) : b0 ≤ p.sharedEnd b0 :=
  (Nat.le_add_right b0 32).trans (wd_ge p b0)



















/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
























end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9





/-- `log 4 = 2 log 2`. -/
theorem log_four : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]

/-- `log 9 = 2 log 3`. -/
theorem log_nine : log 9 = 2 * log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]

/-- `1 ≤ log 4`. -/
theorem one_le_log_four : 1 ≤ log 4 := by
  linarith [log_four, one_half_lt_log_two]


























/-! ### The rounded logarithm `Nat.clog` -/




















end Real

namespace ThreeSumApsp






end ThreeSumApsp

end
end

section


/-!
# 4.4 Choosing the parameters: the entropy function, the exponents `γ` and `q`, equation (11)

Section 4.4 chooses the parameters `L` and `t` of Theorem 30. This file has the facts that its
proofs use about `D = 4^m` and about the notions with which Corollary 31 is stated ("Other choices
of the parameters"). The notation of the paper: `entropy` is `H`, `rhoC c` is `ρ_c = 9/(c-1)`,
`gammaOf c θ` is `γ = θ ln(1/ρ_c)/ln 4`, `qOf θ` is `q = (H(θ) + θ ln 9)/ln 4`, `lnΛ c γ` is the
denominator `ln Λ` of (11), `Rc c γ` is `R_c(γ) = ln 4/ln Λ`, and `D m` is `D = 4^m`.

* The entropy function `H` is Mathlib's `Real.binEntropy` (`entropy_eq_binEntropy`); continuity,
  concavity and the derivative come from there.
* Powers and logarithms of `D = 4^m` (`cast_D_pos`, `one_le_cast_D`, `log_cast_D`,
  `cast_le_log_cast_D`, `cast_D_rpow`).
* The bound `binom(n, k) ≥ e^{n H(k/n)}/(n+1)` (`exp_entropy_div_le_choose`): it is the standard
  bound `binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})`, as `e^{n H(k/n)} = n^n/(k^k (n-k)^{n-k})`.
* One section for each of `ρ_c`, `γ`, `q`, and `ln Λ` with `R_c(γ)`: signs, monotonicity and
  continuity, and the three facts that tie them to the costs: `ρ_c^{θm} = D^{-γ}`
  (`rhoC_rpow_eq_D_rpow`), `e^{m(H(θ) + θ ln 9)} = D^q` (`exp_entropy_eq_D_rpow_qOf`), and
  `Λ < 4^{1/ε}` if and only if `ε < R_c(γ)` (`eq_11_iff`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The entropy function: the link with Mathlib's `Real.binEntropy` -/




































/-! ### Powers and logarithms of `D = 4^m` -/

/-- `ln 4 > 0`. -/
theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- `D = 4^m` as a real number. -/
theorem cast_D_eq (m : ℕ) : (D m : ℝ) = (4 : ℝ) ^ m := by
  simp [D]

/-- `D > 0`. -/
theorem cast_D_pos (m : ℕ) : (0 : ℝ) < (D m : ℝ) := by
  rw [cast_D_eq]
  positivity

/-- `D ≥ 1`. -/
theorem one_le_cast_D (m : ℕ) : (1 : ℝ) ≤ (D m : ℝ) := by
  rw [cast_D_eq]
  exact one_le_pow₀ (by norm_num)

/-- `ln D = m ln 4`. -/
theorem log_cast_D (m : ℕ) : Real.log (D m : ℝ) = (m : ℝ) * Real.log 4 := by
  rw [cast_D_eq, Real.log_pow]

/-- `m ≤ ln D`. -/
theorem cast_le_log_cast_D (m : ℕ) : (m : ℝ) ≤ Real.log (D m : ℝ) := by
  rw [log_cast_D]
  exact le_mul_of_one_le_right (Nat.cast_nonneg m) Real.one_le_log_four

/-- `D^x = e^{x m ln 4}`. -/
theorem cast_D_rpow (m : ℕ) (x : ℝ) :
    (D m : ℝ) ^ x = Real.exp (x * ((m : ℝ) * Real.log 4)) := by
  rw [Real.rpow_def_of_pos (cast_D_pos m), log_cast_D]
  ring_nf

/-! ### The lower bound on binomial coefficients by the entropy function -/































































/-! ### The decay rate `ρ_c` -/

/-- `ρ_c = 9/(c-1) > 0` for `c > 10`. -/
theorem rhoC_pos {c : ℝ} (hc : 10 < c) : 0 < rhoC c := div_pos (by norm_num) (by linarith)



















/-! ### The exponent `γ` -/

/-- `γ` is proportional to `θ`. -/
theorem gammaOf_eq_mul (c θ : ℝ) : gammaOf c θ = θ * gammaOf c 1 := by
  unfold gammaOf
  ring















/-- Proof of Corollary 31: "ρ_c^{θm} = D^{-γ}", with `D = 4^m` and `γ = θ ln(1/ρ_c)/ln 4`. -/
theorem rhoC_rpow_eq_D_rpow (c θ : ℝ) (hc : 10 < c) (m : ℕ) :
    rhoC c ^ (θ * (m : ℝ)) = (D m : ℝ) ^ (-gammaOf c θ) := by
  rw [cast_D_rpow, Real.rpow_def_of_pos (rhoC_pos hc)]
  congr 1
  have hfour := log_four_pos.ne'
  unfold gammaOf
  rw [one_div, Real.log_inv]
  field_simp

/-! ### The exponent `q` -/




















































/-- `e^{m(H(θ) + θ ln 9)} = D^q` with `D = 4^m` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem exp_entropy_eq_D_rpow_qOf (θ : ℝ) (m : ℕ) :
    Real.exp ((m : ℝ) * (entropy θ + θ * Real.log 9)) = (D m : ℝ) ^ qOf θ := by
  rw [cast_D_rpow]
  congr 1
  have hfour := log_four_pos.ne'
  unfold qOf
  field_simp

/-! ### The denominator `ln Λ` of equation (11), and `R_c(γ)` -/



















































end ThreeSumApsp

end
end

section


/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩



























/-! ### Leaving the calculus -/

/-- Two bounds, by nonnegative functions, hold with one constant. -/
theorem exists_const_and (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hg₁ : ∀ x, dom x → 0 ≤ g₁ x) (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f₁ x ≤ C * g₁ x ∧ f₂ x ≤ C * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    ⟨(h₁ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg₁ x hx)),
      (h₂ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg₂ x hx))⟩⟩

/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC

/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩

/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le

/-- Substituting the parameters: a bound in `x` gives a bound in `y` at `x = φ y`, on every domain
that `φ` maps into `dom`. -/
protected theorem comp (hfg : Dominated dom f g) (φ : β → α) {dom' : β → Prop}
    (hφ : ∀ y, dom' y → dom (φ y)) : Dominated dom' (fun y => f (φ y)) fun y => g (φ y) := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun y hy => hf (φ y) (hφ y hy)⟩

/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)






















/-! ### Products and quotients -/




















/-- Both sides may be multiplied from the left by a function that is nonnegative on the domain. -/
theorem mul_left (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => k x * f x) fun x => k x * g x := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hf x hx) (hk x hx)

/-- Both sides may be multiplied from the right by a function that is nonnegative on the domain. -/
theorem mul_right (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => f x * k x) fun x => g x * k x := by
  simpa only [mul_comm] using hfg.mul_left hk
















/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/








































end Dominated












end ThreeSumApsp

end
end

section


/-!
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/

/-- Proof of Corollary 26, "Setting up": for "m := ⌈log_4 D⌉" and `D ≥ 2` the padded inner dimension
satisfies `D ≤ 4^m` and "4^m < 4D", and "the original D was larger than 4^{m-1}". -/
theorem Corollary26.setting_up (D₀ m : ℕ) (hD : 2 ≤ D₀) (hm : m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊) :
    D₀ ≤ D m ∧ D m < 4 * D₀ ∧ 4 ^ (m - 1) < D₀ := by
  obtain rfl : m = Nat.clog 4 D₀ := by
    rw [hm, ← Real.natCeil_logb_natCast]
    norm_num
  have hpos : 1 ≤ Nat.clog 4 D₀ := Nat.clog_pos (by norm_num) hD
  have hlt : 4 ^ (Nat.clog 4 D₀ - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hsucc : 4 ^ Nat.clog 4 D₀ = 4 * 4 ^ (Nat.clog 4 D₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_, hlt⟩
  unfold D
  omega





























/-- The padded inner dimension is at least the given one. -/
theorem Sizes.SetUp.le {p : Sizes} (h : p.SetUp) : p.D₀ ≤ D p.m :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).1

/-- "4^m < 4D". -/
theorem Sizes.SetUp.lt {p : Sizes} (h : p.SetUp) : D p.m < 4 * p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.1

/-- "the original D was larger than 4^{m-1}". -/
theorem Sizes.SetUp.gt {p : Sizes} (h : p.SetUp) : 4 ^ (p.m - 1) < p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.2









/-- Proof of Corollary 26, "Setting up": padding "changes D by a factor less than 4, which only
affects the constants". A bound `D^a log^k D` in the padded `D = 4^m` is, up to a constant, the same
bound in the original inner dimension `D₀`. (Corollary 26 has `k = 0`; the bounds of Corollary 31
have logarithms.) -/
theorem padded_le (a : ℝ) (k : ℕ) :
    Dominated Sizes.SetUp (fun p => (D p.m : ℝ) ^ a * Real.log (D p.m) ^ k)
      fun p => (p.D₀ : ℝ) ^ a * Real.log p.D₀ ^ k := by
  refine .of_le_const_mul (C := 4 ^ |a| * 3 ^ k) (by positivity) fun ⟨D₀, _, m⟩ h => ?_
  have htwo : (2 : ℝ) ≤ D₀ := by exact_mod_cast h.two_le
  have hD₀ : (0 : ℝ) < D₀ := by linarith
  have hle' : 1 ≤ (D m : ℝ) / D₀ := (one_le_div hD₀).2 (by exact_mod_cast h.le)
  have hle4 : (D m : ℝ) ≤ 4 * D₀ := by exact_mod_cast h.lt.le
  have hpow : (D m : ℝ) ^ a ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
    calc (D m : ℝ) ^ a = ((D m : ℝ) / D₀) ^ a * (D₀ : ℝ) ^ a := by
          rw [← Real.mul_rpow (by positivity) hD₀.le, div_mul_cancel₀ _ hD₀.ne']
      _ ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right
            ((Real.rpow_le_rpow_of_exponent_le hle' (le_abs_self a)).trans
              (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hD₀).2 hle4) (abs_nonneg a)))
            (by positivity)
  have hlog : Real.log (D m) ≤ 3 * Real.log D₀ :=
    calc Real.log (D m) ≤ Real.log (4 * D₀) := Real.log_le_log (cast_D_pos m) hle4
      _ = 2 * Real.log 2 + Real.log D₀ := by
          rw [Real.log_mul (by norm_num) hD₀.ne', Real.log_four]
      _ ≤ 3 * Real.log D₀ := by linarith [Real.log_le_log two_pos htwo]
  calc (D m : ℝ) ^ a * Real.log (D m) ^ k
      ≤ 4 ^ |a| * (D₀ : ℝ) ^ a * (3 * Real.log D₀) ^ k :=
        mul_le_mul hpow (pow_le_pow_left₀ (by positivity) hlog k) (by positivity) (by positivity)
    _ = 4 ^ |a| * 3 ^ k * ((D₀ : ℝ) ^ a * Real.log D₀ ^ k) := by
        rw [mul_pow]
        ring





/-- The hypothesis `t ≤ m` of Theorem 30 holds for `t = ⌈θm⌉` with `θ ≤ 1`. -/
theorem switchOf_le {θ : ℝ} (hθ : θ ≤ 1) (m : ℕ) : switchOf θ m ≤ m :=
  Nat.ceil_le.2 (mul_le_of_le_one_left (Nat.cast_nonneg m) hθ)

/-! ### Queries -/




























/-- `(9x)^{θm} (1+1/x)^m = D^q` for "x := (1-θ)/θ". -/
theorem rpow_mul_pow_eq_D_rpow_qOf {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (m : ℕ) :
    (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ)) * (1 + 1 / ((1 - θ) / θ)) ^ m = (D m : ℝ) ^ qOf θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  have hinv : 1 + 1 / ((1 - θ) / θ) = (1 - θ)⁻¹ := by
    field_simp
    ring
  rw [← exp_entropy_eq_D_rpow_qOf, hinv, Real.rpow_def_of_pos (by positivity),
    ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, Real.log_inv,
    Real.log_mul (by norm_num) (by positivity), Real.log_div h1θ.ne' hθ0.ne', entropy]
  congr 1
  ring

/-! ### Encodings -/





/-- Proof of Corollary 26: (10) implies "that the last term of (8) is at most N²/D^γ", "by
rearranging". -/
theorem Equation10.last_term {L m N : ℕ} {γ : ℝ} (h10 : lhs10 L m γ ≤ N) :
    (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ γ := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (cast_D_pos m) γ)]
  calc (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m * (D m : ℝ) ^ γ
      = (N : ℝ) * lhs10 L m γ := by rw [lhs10]; ring
    _ ≤ (N : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 := (sq _).symm

/-- Proof of Corollary 26: (10) implies "that N ≥ √K N₀", "because 10^L ≥ M = K N₀² and D^γ ≥ 1"
(here `γ ≥ 0`). -/
theorem Equation10.tile_fits {L m N : ℕ} (hmL : m ≤ L) {γ : ℝ} (hγ : 0 ≤ γ)
    (h10 : lhs10 L m γ ≤ N) : sqrtKN0 L m ≤ N := by
  have hpos := sqrtKN0_pos hmL
  have hM : sqrtKN0 L m ^ 2 ≤ (10 : ℝ) ^ L := by
    rw [sqrtKN0_sq]
    exact_mod_cast M_le_ten_pow L m
  have hD1 : 1 ≤ (D m : ℝ) ^ γ := Real.one_le_rpow (one_le_cast_D m) hγ
  calc sqrtKN0 L m = sqrtKN0 L m ^ 2 / sqrtKN0 L m := by field_simp
    _ ≤ (10 : ℝ) ^ L / sqrtKN0 L m := div_le_div_of_nonneg_right hM hpos.le
    _ ≤ lhs10 L m γ :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) hD1) hpos.le
    _ ≤ (N : ℝ) := h10

/-! ### Conclusion -/

/-- The expression (8) from its two terms, with `L` and `t` given as functions of `m`. If the first
term, without its factor `N²`, is `O(G)`, where `G ≥ D^{-γ}`, then (8) is `O(G N²)` wherever (10)
holds. -/
theorem dominated_cost8_of_eq_10 {Lof tof : ℕ → ℕ} {γ : ℝ} {G : ℕ → ℝ} {domM : ℕ → Prop}
    {dom : Sizes → Prop}
    (hfirst : Dominated domM
      (fun m => (Lof m : ℝ) * m * (rho (Lof m) m ^ tof m / (1 - rho (Lof m) m))) G)
    (hdom : ∀ p, dom p → domM p.m) (hG : ∀ p, dom p → (D p.m : ℝ) ^ (-γ) ≤ G p.m)
    (h10 : ∀ p, dom p → lhs10 (Lof p.m) p.m γ ≤ p.N) :
    Dominated dom (fun p => cost8 (Lof p.m) p.m (tof p.m) p.N) fun p => G p.m * (p.N : ℝ) ^ 2 := by
  -- the first term of (8), with its factor `N²`
  have hboxes := (hfirst.comp Sizes.m hdom).mul_right (k := fun p => (p.N : ℝ) ^ 2)
    fun _ _ => sq_nonneg _
  -- the last term
  have hencodings : Dominated dom
      (fun p => (p.N : ℝ) * (10 : ℝ) ^ Lof p.m / sqrtKN0 (Lof p.m) p.m)
      fun p => G p.m * (p.N : ℝ) ^ 2 :=
    .of_le fun p hp => (Equation10.last_term (h10 p hp)).trans <| by
      rw [div_eq_mul_inv, mul_comm, ← Real.rpow_neg (cast_D_pos p.m).le]
      exact mul_le_mul_of_nonneg_right (hG p hp) (sq_nonneg _)
  exact hboxes.add hencodings

end ThreeSumApsp

end
end

section


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]



















/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/

/-- Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`. -/
theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [Nat.clog_one_right, hb.le]
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn
    have hlt := Nat.pow_pred_clog_lt_self hb hn
    calc b ^ Nat.clog b n = b * b ^ (Nat.clog b n).pred := by
          rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      _ ≤ b * n := Nat.mul_le_mul_left b hlt.le

end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/















end Real

namespace ThreeSumApsp




end ThreeSumApsp

end
end

section


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/









/-! ## The query -/

namespace Query31










end Query31


























/-- The ceiling ⌈log₄ D⌉ in natural numbers. -/
theorem ceil_logb_four (D₀ : ℕ) : ⌈Real.logb 4 (D₀ : ℝ)⌉₊ = logFour D₀ := by
  have := Real.natCeil_logb_natCast 4 D₀
  simpa [logFour] using this

/-- m ≤ 4 D, because m ≤ 4^m ≤ 4 D. -/
theorem logFour_le_four_mul {D₀ : ℕ} (hD : 1 ≤ D₀) : logFour D₀ ≤ 4 * D₀ :=
  le_trans (Nat.lt_pow_self (by norm_num)).le (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)







end Light.Sec4

end
end

section


/-!
# Theorem 30 in the light language: the two routines against the expressions (8) and L ∑ α_d

Pure arithmetic, continued. Every summand of the time of the shared stage and of the length of the
shared block is at most a constant times `10^L`, or `N (L + 1)`, or the work for the bands
(`sharedShape_le`, `sharedEnd_sub_le`), and these three are within (8). With the tiles of the
previous file this gives the three bounds that leave these two files: the preprocessing takes
`O((8))` steps (`exists_tPreCore_le`), the block has `O((8))` cells (`exists_top_sub_le`), and a
query takes `O(L ∑_{d ≤ t} α_d)` steps (`exists_tQueryAt_le`).  The offline form uses them
elsewhere: its expression (9) is (8) plus |W| times the cost of a query (`Theorem30.cost9_eq`, with
the mathematics of Theorem 30), and `exists_tWantedCore_le`, beside the offline statement, puts the
two bounds together.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The shared stage, in natural numbers -/

/-- `(L + 1)² ≤ 10^L`. -/
theorem succ_sq_le_ten_pow (L : ℕ) : (L + 1) ^ 2 ≤ 10 ^ L := by
  have hfour : (L + 1) ^ 2 ≤ 4 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      calc (L + 1 + 1) ^ 2 ≤ 4 * (L + 1) ^ 2 := by
            rw [show (L + 1 + 1) ^ 2 = L * L + 4 * L + 4 by ring,
              show 4 * (L + 1) ^ 2 = 4 * (L * L) + 8 * L + 4 by ring]
            omega
        _ ≤ 4 * 4 ^ L := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (L + 1) := by ring
  exact hfour.trans (Nat.pow_le_pow_left (by norm_num) L)















private theorem sizeFacts (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    SizeFacts p.L p.m p.K p.KK p.N0 p.D p.S7 p.T :=
  ⟨succ_sq_le_ten_pow p.L, Theorem30.subsets p.L p.m, Theorem30.K_mul_N0_mul_D_le p.L p.m,
    Theorem30.form_array p.L, Nat.pow_le_pow_left (by norm_num) p.L, Nat.sqrt_le _,
    Nat.choose_pos hmL, Nat.one_le_pow _ _ (by norm_num), Nat.one_le_pow _ _ (by norm_num), hL1,
    hmL⟩







































/-- The length of the shared block. -/
theorem sharedEnd_sub_le (p : Sec2.Par) (b0 : ℕ) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    p.sharedEnd b0 - b0 ≤ 190 * 10 ^ p.L + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * 10 ^ p.L) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  change _ ≤ 190 * p.T + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * p.T)
  generalize p.T = T at *
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.N0 = N0 at *
  generalize p.D = D at *
  generalize p.nB = nB at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have hLT : L + 1 ≤ T := (Nat.le_self_pow (by norm_num) _).trans sq
  have hDS : D ≤ S7 := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos K1 N1)) KND
  have hmask : KK * L ≤ K * L := Nat.mul_le_mul_right _ KKle
  have hdig3 : N * Lo ≤ N * L := Nat.mul_le_mul_left _ hLo
  have hdig4 : D * m ≤ L * S7 := (Nat.mul_le_mul hDS mL).trans (le_of_eq (Nat.mul_comm _ _))
  rw [Nat.mul_add_one N L]
  omega

/-! ## Within (8) -/









































































/-- The length of the block, split into the shared block, the scratch strings, and the tries with
their roots. -/
theorem top_sub_eq (p : Sec2.Par) (t b0 : ℕ) :
    top p t b0 - b0 = (p.sharedEnd b0 - b0) + (3 * p.L + p.m + 2)
      + (1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card)) + p.nB * p.nB) := by
  have := base_le_sharedEnd p b0
  simp only [top, aTR, aROOTS, aFP, aSS, aBOX, aCUR, aWD, trieCap]
  omega




























end Light.Sec4

end
end

section


/-!
# Theorem 30 in the light language: limits that are polynomial in N

"Word size", proof of Theorem 30.  For every exponent c of the bound N^c on the entries there are
limits (`lim30`) that the two routines preCore and queryAt can live with (`lim30_ok`) and that are
at most 2^9 ((N + 1) (D + 1))^(20 + 2c) (`small_lim30`).  The exponents are generous: since (10^L)²
≤ N^5, every quantity that depends on L is at most B = (N + 1)^5 (`below`), the block has at most
222 B⁴ cells (`top_sub_le_pow`), and the word bound `word30` is a sum of seven terms, each at most a
small multiple of (N + 1)^(20 + 2c) (`word30_le`).  What the two routines ask of the limits is
`Lim30`, in their specifications.  The polynomial bound is for a block whose base address b0 is at
most 10 (N + 1)³; the end theorems, which put the block behind the input, show this of their b0
(`b0_le`, `wantedB0_le`, `blockAt_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-- There are at most `11^L` cubes. -/
theorem card_boxes_le (L m t : ℕ) : (boxes L m t).card ≤ 11 ^ L := by
  have hsymbols : Fintype.card CubeSymbol = 11 := rfl
  calc (boxes L m t).card ≤ (univ : Finset (Cube L)).card := card_filter_le _ _
    _ = 11 ^ L := by rw [card_univ, Fintype.card_fun, hsymbols, Fintype.card_fin]

/-- The number of bands is at most `N + 1`. -/
theorem numBands_le (L m N : ℕ) (hmL : m ≤ L) : numBands L m N ≤ N + 1 := by
  have hband : 1 ≤ bandSize L m :=
    Nat.mul_pos (Nat.sqrt_pos.mpr (Nat.choose_pos hmL)) (Nat.one_le_pow _ _ (by norm_num))
  have hN : N ≤ bandSize L m * N := Nat.le_mul_of_pos_left _ hband
  refine Nat.div_le_of_le_mul ?_
  rw [Nat.mul_add_one]
  omega

/-- `N₀ ≤ N` under the hypotheses of Theorem 30. -/
theorem N0_le_N {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : N0 p.L p.m ≤ p.N := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (K p.L p.m : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL)
  exact_mod_cast (le_mul_of_one_le_left (Nat.cast_nonneg _) hsqrt).trans h.N_ge





















/-- "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}": so all these quantities are at
most `(10^L)² ≤ N^5`. -/
theorem below {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : Below p t ((p.N + 1) ^ 5) := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsq := Theorem30.ten_pow_le p.L p.m p.N h.L_ge (N0_le_N h)
  have hN5 : p.N ^ 5 ≤ (p.N + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hten : 10 ^ p.L ≤ (10 ^ p.L) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hT : 10 ^ p.L ≤ (p.N + 1) ^ 5 := by omega
  have hN1 : p.N + 1 ≤ (p.N + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hL1 : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h11 : 11 ^ p.L ≤ (10 ^ p.L) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact ⟨by omega, hT, (Nat.pow_le_pow_left (by norm_num) _).trans hT,
    (hL1.trans (succ_sq_le_ten_pow p.L)).trans hT,
    (Nat.pow_le_pow_right (by norm_num) hmL).trans hT,
    (card_boxes_le _ _ _).trans (by omega), (numBands_le p.L p.m p.N hmL).trans hN1, by omega⟩

/-- The length of the block is at most `222 B⁴`. -/
theorem top_sub_le_pow {p : Sec2.Par} {t B : ℕ} (h : Hyp30 p t) (hB : Below p t B) (b0 : ℕ) :
    top p t b0 - b0 ≤ 222 * B ^ 4 := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hL1 : 1 ≤ p.L := by have := h.L_ge; have := h.m_pos; omega
  obtain ⟨hone, hT, -, hL, -, hbx, hnB, hN⟩ := hB
  have hshared := sharedEnd_sub_le p b0 hL1 hmL
  rw [top_sub_eq]
  generalize p.sharedEnd b0 - b0 = E at *
  generalize (boxes p.L p.m t).card = bx at *
  generalize p.nB = nB at *
  generalize 10 ^ p.L = T at *
  -- each product of two of the quantities is at most B², and so on
  have hNL : p.N * (p.L + 1) ≤ B * B := Nat.mul_le_mul hN hL
  have hnT : nB * T ≤ B * B := Nat.mul_le_mul hnB hT
  have hnn : nB * nB ≤ B * B := Nat.mul_le_mul hnB hnB
  have hLb : p.L * bx ≤ B * B := Nat.mul_le_mul (by omega) hbx
  have htries : nB * nB * (11 * (1 + p.L * bx)) ≤ B * B * (11 * (B + B * B)) :=
    Nat.mul_le_mul hnn (by omega)
  -- and every power of B up to the fourth is at most B⁴
  have hpow : ∀ j ≤ 4, B ^ j ≤ B ^ 4 := fun j hj => Nat.pow_le_pow_right hone hj
  have hB0 := hpow 0 (by norm_num)
  have hB1 := hpow 1 (by norm_num)
  have hB2 := hpow 2 (by norm_num)
  have hB3 := hpow 3 (by norm_num)
  rw [pow_zero] at hB0
  rw [pow_one] at hB1
  rw [show B ^ 2 = B * B by ring] at hB2
  rw [show B ^ 3 = B * B * B by ring] at hB3
  rw [show B * B * (11 * (B + B * B)) = 11 * (B * B * B) + 11 * B ^ 4 by ring] at htries
  omega








































































































end Light.Sec4

end
end

section


/-!
# The numerical toolkit for Table 2

Table 2 and the proof of Corollary 26 evaluate the exponents `q(θ)` and `γ = θ ln(1/ρ_c)/ln 4` of
Corollary 31 and the bound `R_c(γ)` of (11) at rational points. All three are built from logarithms
of rational numbers. This file turns each such claim into inequalities between rational numbers,
which the tactic `numerics` checks by evaluating both sides.

* `log_mem` encloses `log θ`: write `θ = 2^k (1 + x)/(1 - x)` with `2^k` near `θ`, and sum `n` terms
  of `log ((1 + x)/(1 - x)) = 2 (x + x³/3 + x⁵/5 + ⋯)`.
* `qOf_le` and `le_qOf` bound `q(θ)` at a rational `θ`.
* `gammaOf_one_mem`, `lnΛ_zero_mem`, `lt_Rc_of_lnΛ_zero_mem` and `Rc_lt_of_lnΛ_zero_mem` treat the
  two numbers on which a row of the table depends: `ln(1/ρ_c)/ln 4` and the denominator of (11) at
  `γ = 0`.
* `Table2Query.intro`, `Table2Ninth.intro` and `Table2Density.intro` give an entry of the table from
  two rational numbers that enclose its `θ`; the `θ` itself comes from the intermediate value
  theorem.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Logarithms of rational numbers -/













/-- A lower bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenLo : ℝ := 2.3025850922

/-- An upper bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenHi : ℝ := 2.3025850938





















private lemma log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The enclosure of `log θ`, between two rational numbers if `θ` is rational. It holds for every
`k` and `n`; they decide only how tight it is. -/
theorem log_mem (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                                     ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                                     ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                                     Finset.sum_range_succ, ThreeSumApsp.rhoC]) :
    Real.log θ ∈ Set.Icc (logApprox k n θ - logErr k n θ) (logApprox k n θ + logErr k n θ) := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hx : |seriesArg k θ| < 1 := by
    rw [seriesArg, abs_div, abs_of_pos (add_pos hθ hpow), div_lt_one (add_pos hθ hpow), abs_lt]
    constructor <;> linarith
  have hsq : 0 < 1 - seriesArg k θ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 hx)
  -- `log θ = k log 2 + log ((1 + x)/(1 - x))`
  have hlog : Real.log θ
      = k * Real.log 2 + Real.log ((1 + seriesArg k θ) / (1 - seriesArg k θ)) := by
    have hdiv : (1 + seriesArg k θ) / (1 - seriesArg k θ) = θ / 2 ^ k := by
      rw [seriesArg]
      field_simp
      ring
    rw [hdiv, Real.log_div hθ.ne' hpow.ne', Real.log_zpow]
    ring
  have htwo : |k * Real.log 2 - k * ((logTwoLo + logTwoHi) / 2)|
      ≤ |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [log_two_mem.1, log_two_mem.2]
  -- Mathlib: the sum of `n` terms differs from `½ log ((1 + x)/(1 - x))` by at most
  -- `|x|^(2n+1)/(1 - x²)`. We use `|x|^(2n+1) ≤ x^(2n)`, which is free of absolute values.
  have hseries := (Real.sum_range_sub_log_div_le hx n).trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx.le (Nat.le_succ _)) hsq.le)
  rw [(even_two_mul n).pow_abs] at hseries
  rw [abs_le] at htwo hseries
  rw [hlog, logApprox, logErr]
  constructor <;> linarith [htwo.1, htwo.2, hseries.1, hseries.2]

private lemma log_three_mem : Real.log 3 ∈ Set.Icc logThreeLo logThreeHi :=
  ⟨le_trans (by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                    ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                    ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                    Finset.sum_range_succ, ThreeSumApsp.rhoC]) (log_mem 2 7).1, (log_mem 2 7).2.trans (by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                                                                            ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                                                                            ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                                                                            Finset.sum_range_succ, ThreeSumApsp.rhoC])⟩




/-! ## The exponent `q` of the query time (Corollary 31) -/

/-- `q(θ)` written out in terms of `log 2` and `log 3`. -/
private lemma qOf_eq_div (θ : ℝ) :
    qOf θ = (-θ * Real.log θ - (1 - θ) * Real.log (1 - θ) + θ * (2 * Real.log 3))
      / (2 * Real.log 2) := by
  unfold qOf entropy
  rw [Real.log_four, Real.log_nine]

/-- An upper bound on `q(θ)` at a rational `θ`. The hypothesis `h` is `H(θ) + θ ln 9 ≤ r ln 4` with
every logarithm replaced by the bound that makes the inequality harder. Here `2^k` is the power of
two nearest to `θ`; four terms of the series for `log θ` and for `log (1 - θ)` are enough for every
entry of Table 2. -/
theorem qOf_le (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                           ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                           ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                           Finset.sum_range_succ, ThreeSumApsp.rhoC]) (h1 : θ < 1 := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                                                                                           ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                                                                                           ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                                                                                           Finset.sum_range_succ, ThreeSumApsp.rhoC])
    (hr : 0 ≤ r := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                          ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                          ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                          Finset.sum_range_succ, ThreeSumApsp.rhoC])
    (h : -θ * (logApprox k 4 θ - logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) - logErr 0 4 (1 - θ)) + θ * (2 * logThreeHi)
      ≤ r * (2 * logTwoLo) := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                     ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                     ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                     Finset.sum_range_succ, ThreeSumApsp.rhoC]) : qOf θ ≤ r := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  rw [qOf_eq_div, div_le_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).1 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).1 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.2 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.1 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-- A lower bound on `q(θ)` at a rational `θ`, computed as in `qOf_le`. -/
theorem le_qOf (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                           ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                           ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                           Finset.sum_range_succ, ThreeSumApsp.rhoC]) (h1 : θ < 1 := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                                                                                           ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                                                                                           ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                                                                                           Finset.sum_range_succ, ThreeSumApsp.rhoC])
    (hr : 0 ≤ r := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                          ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                          ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                          Finset.sum_range_succ, ThreeSumApsp.rhoC])
    (h : r * (2 * logTwoHi)
      ≤ -θ * (logApprox k 4 θ + logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) + logErr 0 4 (1 - θ)) + θ * (2 * logThreeLo) := by
      norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
        ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
        ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
        Finset.sum_range_succ, ThreeSumApsp.rhoC]) : r ≤ qOf θ := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  rw [qOf_eq_div, le_div_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).2 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).2 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.1 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.2 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-! ## The exponent `γ` (Corollary 31) -/

/-- Bounds on `γ` at `θ = 1`, that is on `ln(1/ρ_c)/ln 4`, from bounds on `ln(1/ρ_c)`. -/
theorem gammaOf_one_mem {c a b glo ghi : ℝ} (h : Real.log (1 / rhoC c) ∈ Set.Icc a b)
    (hglo : 0 ≤ glo := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                              ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                              ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                              Finset.sum_range_succ, ThreeSumApsp.rhoC]) (hghi : 0 ≤ ghi := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                                                                                   ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                                                                                   ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                                                                   Finset.sum_range_succ, ThreeSumApsp.rhoC])
    (hlo : glo * (2 * logTwoHi) ≤ a := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                              ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                              ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                              Finset.sum_range_succ, ThreeSumApsp.rhoC])
    (hhi : b ≤ ghi * (2 * logTwoLo) := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg,
                                              ThreeSumApsp.logTwoLo, ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo,
                                              ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                              Finset.sum_range_succ, ThreeSumApsp.rhoC]) : gammaOf c 1 ∈ Set.Icc glo ghi := by
  have hpos : 0 < 2 * Real.log 2 := mul_pos two_pos (Real.log_pos one_lt_two)
  have htwolo := mul_le_mul_of_nonneg_left log_two_mem.2 hglo
  have htwohi := mul_le_mul_of_nonneg_left log_two_mem.1 hghi
  rw [Set.mem_Icc, gammaOf, Real.log_four, one_mul, le_div_iff₀ hpos, div_le_iff₀ hpos]
  exact ⟨by linarith [hlo, htwolo, h.1], by linarith [hhi, htwohi, h.2]⟩









/-! ## The bound `R_c(γ)` (equation (11)) -/

























































/-! ## Entries of Table 2

An entry needs two facts on its row, `hg` (an enclosure of `ln(1/ρ_c)/ln 4`) and `hR` (the `ε` of
the row is below `R_c(γ)` up to the largest `γ` of the row), and two rational numbers `θlo ≤ θhi`
that enclose its `θ`. -/


































































end ThreeSumApsp

end
end

section


/-!
# Table 2

Section 4.4 prescribes how an entry is computed. The left half has the `γ` of Corollary 31, "with
the c of the row and the θ that gives the q of the column (θ = 1/9 for q = 0.43)". The right half
has the `γ` of Corollary 32, "with the θ at which γ = κ - q". "The ε of a row of the table is the
smallest R_c(γ) over its entries." All values are rounded down (caption).

* The `θ` of a column of the left half does not depend on the row. It is enclosed between two
  decimal numbers (`exists_qOf_eq_010` to `exists_qOf_eq_090`): `q(θ)` is at most the `q` of the
  column at the lower number (`qOf_le`) and at least that `q` at the upper number (`le_qOf`), and it
  is continuous.
* A row (`table_2_c40` to `table_2_c10_5`) depends on `c` through two numbers: `ln(1/ρ_c)/ln 4`, by
  which `θ` is multiplied to give `γ` (`hg`), and the denominator of (11) at `γ = 0` (`hB`), which
  gives `ε < R_c(γ)` for every `γ` up to the largest one of the row (`hR`).
* An entry of the left half is `Table2Query.intro` at the enclosure of the `θ` of its column. An
  entry of the right half (`Table2Density.intro`) names two decimal numbers: at the lower one
  `γ + q ≤ κ` (`qOf_le`), at the upper one `γ + q ≥ κ` (`le_qOf`), so the root `θ` of `γ + q = κ`
  lies between them; and `γ = θ ln(1/ρ_c)/ln 4` has the printed four decimals at both.

How to read the numbers in the proofs. The two decimal numbers around a `θ` are `θ` cut after five
decimals and the next such number, or after six decimals where `γ` is too close to a multiple of
`0.0001`. The argument `k` of `qOf_le`, `le_qOf` and `log_mem` is the exponent of the power of two
nearest to the number whose logarithm is taken, and the second argument of `log_mem` is the number
of terms of the series.
-/

public section

open Finset

namespace ThreeSumApsp

/-! ## The `θ` of the columns of the left half -/





















/-- Caption of Table 2: at `θ = 1/9`, "more precisely, q = 0.4277…". -/
theorem qOf_ninth_mem : qOf (1 / 9) ∈ Set.Icc 0.42773 0.42774 :=
  ⟨le_qOf (-3), qOf_le (-3)⟩

/-! ## The six rows -/





















/-- `ln(1/ρ_c)/ln 4` for `c = 21` (the proof of Corollary 26 uses it too). -/
theorem gammaOf_21_one_mem : gammaOf 21 1 ∈ Set.Icc 0.576001 0.576002 :=
  gammaOf_one_mem (log_mem 1 3)




















































































































end ThreeSumApsp

end
end

section


/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/

/-- `log x + 1 = O(x ^ η)` on `x ≥ 1`, for `η > 0`. -/
theorem dominated_log_add_one_rpow {η : ℝ} (hη : 0 < η) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => log x + 1) fun x => x ^ η := by
  refine .of_le_const_mul (C := 1 / η + 1) (by positivity) fun x hx => ?_
  have hlog : log x ≤ x ^ η / η := log_le_rpow_div (zero_le_one.trans hx) hη
  have hone : 1 ≤ x ^ η := one_le_rpow hx hη.le
  rw [add_mul, one_mul, one_div_mul_eq_div]
  exact add_le_add hlog hone

/-- `(log x + 1) ^ e = O(x ^ η)` on `x ≥ 1`, for `η > 0`. -/
theorem dominated_log_add_one_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => (log x + 1) ^ e) fun x => x ^ η := by
  have hstep := (dominated_log_add_one_rpow (div_pos hη (Nat.cast_add_one_pos e))).pow
    (fun x hx => add_nonneg (log_nonneg hx) zero_le_one) e
  refine hstep.mono_right fun x hx => ?_
  rw [← rpow_natCast, ← rpow_mul (zero_le_one.trans hx)]
  refine rpow_le_rpow_of_exponent_le hx ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (Nat.cast_add_one_pos e)]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hη.le

/-- Logarithms are absorbed: `x ^ a * (log x + 1) ^ e = O(x ^ b)` on `x ≥ 1`, for `a < b`. -/
theorem dominated_rpow_mul_log_add_one_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => x ^ a * (log x + 1) ^ e) fun x => x ^ b :=
  ((dominated_log_add_one_pow_rpow (sub_pos.2 hab) e).mul_left
    fun x hx => rpow_nonneg (zero_le_one.trans hx) a).congr (fun _ _ => rfl) fun x hx => by
      rw [← rpow_add (zero_lt_one.trans_le hx), add_sub_cancel]

/-- Logarithms are absorbed: `x ^ a * (log x) ^ e = O(x ^ b)` on `x ≥ 1`, for `a < b`. -/
theorem dominated_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => x ^ a * log x ^ e) fun x => x ^ b :=
  (dominated_rpow_mul_log_add_one_pow_rpow hab e).mono_left fun _ hx =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (log_nonneg hx) (le_add_of_nonneg_right zero_le_one) e)
      (rpow_nonneg (zero_le_one.trans hx) a)

/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/



















end ThreeSumApsp

end
end

section


/-!
# Corollary 26: the parameters `L = 21m`, `t = ⌈m/9⌉`

The proof of Corollary 26 from Theorem 30, in the five steps of the paper. The parts of these steps
that hold for all `L` and `t` are proved before (`Corollary26.setting_up` to
`dominated_cost8_of_eq_10`), and Corollary 31 uses them too. The exponents `γ` and `q` of the proof
are written `gammaOf 21 (1 / 9)` and `qOf (1 / 9)`: they are the `γ` and `q` of Corollary 31 at
`c = 21` and `θ = 1/9` (`Corollary26.gamma_eq`, `Corollary26.q_eq`). The result is
`Corollary26.costs`: for `N ≥ D^18` and `m = ⌈log_4 D⌉ ≥ 60` the hypothesis `N ≥ √K N₀` of Theorem
30 holds at `L = 21m` and `t = ⌈m/9⌉`, its preprocessing cost (8) (`cost8`) is `O(N²/D^{0.063})`,
and its query cost `L ∑_{d ≤ t} α_d` (`costQuery`) is `O(D^{0.437})`.

* Setting up. The inner dimension is padded to `D = 4^m` (`Corollary26.setting_up`). This changes no
  entry of the product (`Corollary26.padding`), it changes the bounds by a constant factor
  (`padded_le`), and the hypothesis reads `N ≥ 4^{18(m-1)}` (`Corollary26.hypothesis`). The number
  `t = ⌈m/9⌉` is `switchOf (1 / 9) m`, and `t ≤ m` (`switchOf_le`).
* Boxes. `ρ < 9/20` and `ρ^t ≤ (9/20)^{m/9} = D^{-γ}` with `γ = 0.0640…` (`Corollary26.rho_lt`,
  `Corollary26.rho_pow_le`, `Corollary26.gamma_digits`), so the first term of (8) is `O(m² N²/D^γ)`
  (`Corollary26.first_term`).
* Queries. `∑_{d ≤ t} α_d ≤ 72^t (9/8)^m < 72 D^q` with `q = 0.4277…` (`sum_alpha_le`,
  `Corollary26.sum_alpha_lt`, `Corollary26.q_digits`), so a query costs `O(m D^q)`
  (`Corollary26.query_cost`).
* Encodings. Inequality (10) bounds the last term of (8) and gives the hypothesis of Theorem 30
  (`Equation10.last_term`, `Equation10.tile_fits`). The standard bound on `K` (`Corollary26.le_K`)
  shows that the left-hand side of (10) is at most `√(21m+1) Λ^m` (`Corollary26.lhs10_le`);
  `Λ = 4.198… · 10^10` is below `4^18 = 6.871… · 10^10` by a factor of more than 1.63
  (`baseLambda_numeric`, `four_pow_eighteen_numeric`, `baseLambda_mul_lt`), and
  `1.63^m ≥ 4^18 √(21m+1)` for `m ≥ 60` (`Corollary26.threshold`). Together they give (10) for all
  `m ≥ 60` (`eq_10_corollary_26`).
* Conclusion. For `m ≥ 60` the hypothesis `N ≥ √K N₀` holds and (8) is `O(m² N²/D^γ)`
  (`Corollary26.tile_fits`, `dominated_cost8_of_eq_10`, `Corollary26.preprocessing`), the powers of
  `m` are absorbed into the exponents (`dominated_pow_mul_D_rpow`, `Corollary26.conclusion`), and
  the bounds are stated in the given `D` (`Corollary26.costs`). For `|W| ≤ N²/√D` queries the total
  is `O(N²/D^{0.063})` (`corollary_26_W`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given `D`, of `N` and of `m`. Two sentences of the proof are proved with the programs
(`wordRam_corollary_26`, `wordRam_corollary_26_wanted`): "(For m < 60, D is bounded by a constant,
and the corollary holds trivially.)" and "The bound for a set W follows by asking |W| queries." The
last section shows that the parameters of this proof are those of Corollary 31 and of Table 2 at
`c = 21` and `θ = 1/9`; nothing else rests on it.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/

/-- Proof of Corollary 26, "Setting up": "since the original D was larger than 4^{m-1}, the
assumption N ≥ D^18 now reads N ≥ 4^{18(m-1)}". -/
theorem Corollary26.hypothesis {D₀ N m : ℕ} (hgt : 4 ^ (m - 1) < D₀) (hN : D₀ ^ 18 ≤ N) :
    4 ^ (18 * (m - 1)) ≤ N := by
  rw [mul_comm, pow_mul]
  exact (Nat.pow_le_pow_left hgt.le 18).trans hN

/-! ### Boxes -/

/-- Proof of Corollary 26: "ρ = 9m/(L-m+1) = 9m/(20m+1) < 9/20, so 1/(1-ρ) < 2". -/
theorem Corollary26.rho_lt (m : ℕ) :
    rho (21 * m) m = 9 * (m : ℝ) / (20 * (m : ℝ) + 1) ∧ rho (21 * m) m < 9 / 20 ∧
      1 / (1 - rho (21 * m) m) < 2 := by
  have heq : rho (21 * m) m = 9 * (m : ℝ) / (20 * (m : ℝ) + 1) := by
    rw [rho]
    push_cast
    ring_nf
  have hlt : rho (21 * m) m < 9 / 20 := by
    rw [heq, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨heq, hlt, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- Proof of Corollary 26: "since t ≥ m/9, also ρ^t ≤ (9/20)^{m/9} = D^{-γ}". -/
theorem Corollary26.rho_pow_le (m : ℕ) :
    rho (21 * m) m ^ switchOf (1 / 9) m ≤ (9 / 20 : ℝ) ^ ((m : ℝ) / 9) ∧
      (9 / 20 : ℝ) ^ ((m : ℝ) / 9) = (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) := by
  obtain ⟨-, hlt, -⟩ := Corollary26.rho_lt m
  constructor
  · calc rho (21 * m) m ^ switchOf (1 / 9) m
        ≤ (9 / 20 : ℝ) ^ switchOf (1 / 9) m :=
          pow_le_pow_left₀ (rho_nonneg (by omega)) hlt.le _
      _ = (9 / 20 : ℝ) ^ ((switchOf (1 / 9) m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (9 / 20 : ℝ) ^ ((m : ℝ) / 9) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
            ((by ring_nf : (m : ℝ) / 9 = 1 / 9 * m).le.trans (Nat.le_ceil _))
  · -- `ρ_c = 9/20` at `c = 21`
    have h := rhoC_rpow_eq_D_rpow 21 (1 / 9) (by norm_num) m
    rwa [show rhoC 21 = 9 / 20 by norm_num [rhoC], show (1 / 9 : ℝ) * m = m / 9 by ring] at h

/-- Proof of Corollary 26: "γ := ln(20/9)/(9 ln 4)". This is the `γ` of Corollary 31 at `c = 21` and
`θ = 1/9`, where `ρ_c = 9/20`; the statements of this file write it `gammaOf 21 (1 / 9)`. -/
theorem Corollary26.gamma_eq : gammaOf 21 (1 / 9) = Real.log (20 / 9) / (9 * Real.log 4) := by
  have hfour : Real.log 4 ≠ 0 := log_four_pos.ne'
  rw [gammaOf, rhoC, show (1 / (9 / (21 - 1)) : ℝ) = 20 / 9 by norm_num]
  field_simp

/-- Proof of Corollary 26: "γ := ln(20/9)/(9 ln 4) = 0.0640…". The digits come from the bounds on
logarithms proved for Table 2. -/
theorem Corollary26.gamma_digits : 0.0640 < gammaOf 21 (1 / 9) ∧ gammaOf 21 (1 / 9) < 0.0641 := by
  have heq := gammaOf_eq_mul 21 (1 / 9)
  have hmem := gammaOf_21_one_mem
  exact ⟨by linarith [heq, hmem.1], by linarith [heq, hmem.2]⟩

/-- Proof of Corollary 26: "Hence the first term of (8) is O(m² N²/D^γ)". The common factor `N²` is
left out. -/
theorem Corollary26.first_term :
    Dominated (fun _ : ℕ => True)
      (fun m => ((21 * m : ℕ) : ℝ) * m *
        (rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m)))
      fun m => (m : ℝ) ^ 2 * (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) := by
  refine .of_le_const_mul (C := 42) (by norm_num) fun m _ => ?_
  obtain ⟨-, hlt, htwo⟩ := Corollary26.rho_lt m
  obtain ⟨hpow, heq⟩ := Corollary26.rho_pow_le m
  rw [heq] at hpow
  -- `ρ^t/(1-ρ) ≤ 2 D^{-γ}`
  have hdecay : rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m)
      ≤ (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) * 2 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hpow htwo.le (one_div_nonneg.2 (by linarith)) (by positivity)
  calc ((21 * m : ℕ) : ℝ) * m * (rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m))
      ≤ ((21 * m : ℕ) : ℝ) * m * ((D m : ℝ) ^ (-gammaOf 21 (1 / 9)) * 2) := by
        gcongr
    _ = 42 * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-gammaOf 21 (1 / 9))) := by
        push_cast
        ring

/-! ### Queries -/

/-- `72^{m/9} (9/8)^m = D^q`: at `θ = 1/9` the number `x = (1-θ)/θ` is 8. -/
private lemma rpow_div_nine_eq (m : ℕ) :
    (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m = (D m : ℝ) ^ qOf (1 / 9) := by
  have h := rpow_mul_pow_eq_D_rpow_qOf (θ := 1 / 9) (by norm_num) (by norm_num) m
  rwa [show (9 * ((1 - 1 / 9) / (1 / 9)) : ℝ) = 72 by norm_num,
    show (1 + 1 / ((1 - 1 / 9) / (1 / 9)) : ℝ) = 9 / 8 by norm_num,
    show (1 / 9 : ℝ) * m = m / 9 by ring] at h

/-- Proof of Corollary 26, the display of the step "Queries": "∑_{d=0}^{t} binom(m, d) 9^d ≤ 72^t
∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m < 72 · (72 · (9/8)^9)^{m/9} = 72 D^q", with
`t = ⌈m/9⌉`. -/
theorem Corollary26.sum_alpha_lt (m : ℕ) :
    ∑ d ∈ range (switchOf (1 / 9) m + 1), (alpha m d : ℝ) < 72 * (D m : ℝ) ^ qOf (1 / 9) := by
  set t : ℕ := switchOf (1 / 9) m
  have htm : t ≤ m := switchOf_le (by norm_num) m
  -- "t < m/9 + 1"
  have htlt : (t : ℝ) < (m : ℝ) / 9 + 1 := by
    have h : (t : ℝ) < 1 / 9 * (m : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ (9 * 8) ^ t * (1 + 1 / 8 : ℝ) ^ m := sum_alpha_le (by norm_num) (by norm_num) htm
    _ = 72 ^ t * (9 / 8 : ℝ) ^ m := by norm_num
    _ < 72 * (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m := by
        gcongr
        calc (72 : ℝ) ^ t = (72 : ℝ) ^ (t : ℝ) := (Real.rpow_natCast _ _).symm
          _ < (72 : ℝ) ^ ((m : ℝ) / 9 + 1) :=
              Real.rpow_lt_rpow_of_exponent_lt (by norm_num) htlt
          _ = 72 * (72 : ℝ) ^ ((m : ℝ) / 9) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
    _ = 72 * (D m : ℝ) ^ qOf (1 / 9) := by
        rw [mul_assoc, rpow_div_nine_eq]















/-- Proof of Corollary 26: "q := ln(72 · (9/8)^9)/(9 ln 4) = 0.4277…". The digits come from the
bounds on logarithms proved for Table 2. -/
theorem Corollary26.q_digits : 0.4277 < qOf (1 / 9) ∧ qOf (1 / 9) < 0.4278 :=
  ⟨lt_of_lt_of_le (by norm_num) qOf_ninth_mem.1, lt_of_le_of_lt qOf_ninth_mem.2 (by norm_num)⟩

/-- Proof of Corollary 26: "Hence a query takes O(L D^q) = O(m D^q) time." -/
theorem Corollary26.query_cost :
    Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
      fun m => (m : ℝ) * (D m : ℝ) ^ qOf (1 / 9) := by
  refine .of_le_const_mul (C := 21 * 72) (by norm_num) fun m _ => ?_
  calc costQuery (21 * m) m (switchOf (1 / 9) m)
      ≤ ((21 * m : ℕ) : ℝ) * (72 * (D m : ℝ) ^ qOf (1 / 9)) :=
        mul_le_mul_of_nonneg_left (Corollary26.sum_alpha_lt m).le (Nat.cast_nonneg _)
    _ = 21 * 72 * ((m : ℝ) * (D m : ℝ) ^ qOf (1 / 9)) := by
        push_cast
        ring

/-! ### Encodings -/































/-- Proof of Corollary 26: "the left-hand side of (10) is at most √(21m+1) · Λ^m". -/
theorem Corollary26.lhs10_le {m : ℕ} (hm : 1 ≤ m) :
    lhs10 (21 * m) m (gammaOf 21 (1 / 9)) ≤ Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := by
  -- "D^γ = (20/9)^{m/9}, 10^L = 10^{21m}, and N₀ = 3^{20m}"
  have hD : (D m : ℝ) ^ gammaOf 21 (1 / 9) = ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m := by
    have hfour := log_four_pos.ne'
    rw [Corollary26.gamma_eq, cast_D_rpow, ← Real.rpow_mul_natCast (by norm_num),
      Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  have hN0 : (N0 (21 * m) m : ℝ) = ((3 : ℝ) ^ 20) ^ m := by
    rw [N0, show 21 * m - m = 20 * m by omega, pow_mul]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hroot : 0 < Real.sqrt (21 * (m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hs : 0 < Real.sqrt (21 ^ 21 / 20 ^ 20) := Real.sqrt_pos.2 (by positivity)
  -- the bound on `K`, under the square root
  have hK : Real.sqrt (21 ^ 21 / 20 ^ 20) ^ m / Real.sqrt (21 * (m : ℝ) + 1)
      ≤ Real.sqrt (K (21 * m) m) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    exact Corollary26.le_K hm
  rw [lhs10, sqrtKN0, hD, hN0, pow_mul]
  calc ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m * ((10 : ℝ) ^ 21) ^ m
        / (Real.sqrt (K (21 * m) m) * ((3 : ℝ) ^ 20) ^ m)
      ≤ ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m * ((10 : ℝ) ^ 21) ^ m
        / (Real.sqrt (21 ^ 21 / 20 ^ 20) ^ m / Real.sqrt (21 * (m : ℝ) + 1)
          * ((3 : ℝ) ^ 20) ^ m) := by
        gcongr
    _ = Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := by
        rw [baseLambda, div_pow, mul_pow, mul_pow]
        field_simp

/-- Proof of Corollary 26: `Λ` "= 4.198… · 10^10". Eighteenth powers are compared: `Λ^18` is a
rational number. -/
theorem baseLambda_numeric : 4.198 * 10 ^ 10 < baseLambda ∧ baseLambda < 4.199 * 10 ^ 10 := by
  have hpow : baseLambda ^ 18
      = (10 ^ 21) ^ 18 * (20 / 9) ^ 2 / ((21 ^ 21 / 20 ^ 20) ^ 9 * (3 ^ 20) ^ 18) := by
    rw [baseLambda, div_pow, mul_pow, mul_pow, ← Real.rpow_mul_natCast (by norm_num),
      pow_mul (Real.sqrt _) 2 9, Real.sq_sqrt (by positivity)]
    norm_num
  exact ⟨lt_of_pow_lt_pow_left₀ 18 (by unfold baseLambda; positivity) (by rw [hpow]; norm_num),
    lt_of_pow_lt_pow_left₀ 18 (by norm_num) (by rw [hpow]; norm_num)⟩

/-- Proof of Corollary 26: "Its base 4^18 = 6.871… · 10^10". -/
theorem four_pow_eighteen_numeric :
    6.871 * 10 ^ 10 < (4 : ℝ) ^ 18 ∧ (4 : ℝ) ^ 18 < 6.872 * 10 ^ 10 := by
  constructor <;> norm_num

/-- Proof of Corollary 26: `4^18` "is larger than Λ by a factor of more than 1.63". -/
theorem baseLambda_mul_lt : 1.63 * baseLambda < 4 ^ 18 :=
  calc 1.63 * baseLambda < 1.63 * (4.199 * 10 ^ 10) :=
        mul_lt_mul_of_pos_left baseLambda_numeric.2 (by norm_num)
    _ < 6.871 * 10 ^ 10 := by norm_num
    _ < 4 ^ 18 := four_pow_eighteen_numeric.1


















/-- Equation (10), `D^γ · 10^L / (√K N₀) ≤ N`, where it is printed, in the proof of Corollary 26.
There `D = 4^m`, "L := 21m", "γ := ln(20/9)/(9 ln 4)", "K = binom(21m, m)", "N₀ = 3^{20m}", and "the
assumption N ≥ D^18 now reads N ≥ 4^{18(m-1)}". The inequality "holds whenever
1.63^m ≥ 4^18 √(21m+1), which is the case for all m ≥ 60". -/
theorem eq_10_corollary_26 (m N : ℕ) (hm : 60 ≤ m) (hN : 4 ^ (18 * (m - 1)) ≤ N) :
    (D m : ℝ) ^ (Real.log (20 / 9) / (9 * Real.log 4)) * (10 : ℝ) ^ (21 * m)
        / (Real.sqrt (K (21 * m) m) * (N0 (21 * m) m : ℝ))
      ≤ (N : ℝ) := by
  have hΛ0 : 0 ≤ baseLambda := by linarith [baseLambda_numeric.1]
  have hΛ : baseLambda ≤ 4 ^ 18 / 1.63 := by
    rw [le_div_iff₀' (by norm_num)]
    exact baseLambda_mul_lt.le
  rw [← Corollary26.gamma_eq]
  calc lhs10 (21 * m) m (gammaOf 21 (1 / 9))
      ≤ Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := Corollary26.lhs10_le (by omega)
    _ ≤ Real.sqrt (21 * (m : ℝ) + 1) * ((4 : ℝ) ^ 18 / 1.63) ^ m := by gcongr
    _ = (4 : ℝ) ^ 18 * Real.sqrt (21 * (m : ℝ) + 1) / 1.63 ^ m * (4 : ℝ) ^ (18 * (m - 1)) := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, div_pow, ← pow_mul]
        field_simp
        ring
    _ ≤ 1 * (4 : ℝ) ^ (18 * (m - 1)) := by
        gcongr
        exact (div_le_one (by positivity)).2 (Corollary26.threshold hm)
    _ ≤ (N : ℝ) := by
        rw [one_mul]
        exact_mod_cast hN

/-! ### Conclusion -/






/-- Inequality (10) holds in this range (`eq_10_corollary_26`). -/
theorem Sizes.Large26.lhs10_le {p : Sizes} (h : p.Large26) :
    lhs10 (21 * p.m) p.m (gammaOf 21 (1 / 9)) ≤ p.N := by
  rw [Corollary26.gamma_eq]
  exact eq_10_corollary_26 p.m p.N h.m_ge h.N_ge

/-- Proof of Corollary 26, "Conclusion": "For m ≥ 60, Theorem 30 thus applies": its hypothesis
`N ≥ √K N₀` holds. -/
theorem Corollary26.tile_fits {p : Sizes} (h : p.Large26) : sqrtKN0 (21 * p.m) p.m ≤ p.N :=
  Equation10.tile_fits (by omega) (by linarith [Corollary26.gamma_digits.1]) h.lhs10_le

/-- Proof of Corollary 26, "Conclusion": "The preprocessing takes O(m² N²/D^γ) time and space". -/
theorem Corollary26.preprocessing :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
      fun p => (p.m : ℝ) ^ 2 * (D p.m : ℝ) ^ (-gammaOf 21 (1 / 9)) * (p.N : ℝ) ^ 2 :=
  dominated_cost8_of_eq_10 (Lof := fun m => 21 * m) Corollary26.first_term (fun _ _ => trivial)
    (fun p hp => le_mul_of_one_le_left (by positivity)
      (one_le_pow₀ (Nat.one_le_cast.2 (le_trans (by norm_num) hp.m_ge))))
    fun _ hp => hp.lhs10_le

/-- Proof of Corollary 26, "Conclusion": "Since m = O(log D) and the exponents γ - 0.063 and 0.437 -
q are positive, we have m² = O(D^{γ-0.063}) and m = O(D^{0.437-q})". In general, `m^e D^a = O(D^b)`
for `D = 4^m` and `a < b`. -/
theorem dominated_pow_mul_D_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun _ : ℕ => True) (fun m => (m : ℝ) ^ e * (D m : ℝ) ^ a)
      fun m => (D m : ℝ) ^ b := by
  refine ((dominated_rpow_mul_log_pow_rpow hab e).comp (fun m : ℕ => (D m : ℝ))
    fun m (_ : True) => one_le_cast_D m).mono_left fun m _ => ?_
  have hm := cast_le_log_cast_D m
  rw [mul_comm]
  gcongr

/-- Proof of Corollary 26, "Conclusion", with `D = 4^m`: "which gives the bounds O(N²/D^{0.063}) and
O(D^{0.437}) of the corollary". -/
theorem Corollary26.conclusion :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
        (fun p => (D p.m : ℝ) ^ (-0.063 : ℝ) * (p.N : ℝ) ^ 2) ∧
      Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
        fun m => (D m : ℝ) ^ (0.437 : ℝ) := by
  -- "the exponents γ - 0.063 and 0.437 - q are positive"
  have hγ : -gammaOf 21 (1 / 9) < -0.063 := by linarith [Corollary26.gamma_digits.1]
  have hq : qOf (1 / 9) < 0.437 := by linarith [Corollary26.q_digits.2]
  exact ⟨Corollary26.preprocessing.trans
      (((dominated_pow_mul_D_rpow hγ 2).comp Sizes.m fun _ _ => trivial).mul_right
        fun _ _ => sq_nonneg _),
    Corollary26.query_cost.trans (by simpa only [pow_one] using dominated_pow_mul_D_rpow hq 1)⟩







/-- `D ≥ 2`, since `m = 0` for `D ≤ 1`. -/
theorem Sizes.Corollary26.setUp {p : Sizes} (h : p.Corollary26) : p.SetUp := by
  obtain ⟨-, hm, hm60⟩ := h
  refine ⟨?_, hm⟩
  by_contra hlt
  obtain h0 | h1 : p.D₀ = 0 ∨ p.D₀ = 1 := by omega
  · simp only [h0, Nat.cast_zero, Real.logb_zero, Nat.ceil_zero] at hm
    omega
  · simp only [h1, Nat.cast_one, Real.logb_one, Nat.ceil_zero] at hm
    omega

/-- After "Setting up", these instances are in the range of the step "Conclusion". -/
theorem Sizes.Corollary26.large {p : Sizes} (h : p.Corollary26) : p.Large26 :=
  ⟨h.m_ge, Corollary26.hypothesis h.setUp.gt h.N_ge⟩

/-- Corollary 26, the costs of Theorem 30 at "L := 21m and t := ⌈m/9⌉", in terms of the given `D`:
there is a constant `C` such that for all `N ≥ D^{18}` with `m = ⌈log_4 D⌉ ≥ 60` the hypothesis
`N ≥ √K N₀` of Theorem 30 holds, the expression (8) is at most `C N²/D^{0.063}`, and the query cost
is at most `C D^{0.437}`. -/
theorem Corollary26.costs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D₀ N m : ℕ, D₀ ^ 18 ≤ N → m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → 60 ≤ m →
      sqrtKN0 (21 * m) m ≤ N ∧
      cost8 (21 * m) m (switchOf (1 / 9) m) N ≤ C * ((N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)) ∧
      costQuery (21 * m) m (switchOf (1 / 9) m) ≤ C * (D₀ : ℝ) ^ (0.437 : ℝ) := by
  -- the padding "changes D by a factor less than 4, which only affects the constants"
  have hpad : ∀ a : ℝ, Dominated Sizes.Corollary26 (fun p => (D p.m : ℝ) ^ a)
      fun p => (p.D₀ : ℝ) ^ a := fun a => by
    simpa only [pow_zero, mul_one] using (padded_le a 0).mono_dom fun _ hp => hp.setUp
  have hpre := ((Corollary26.conclusion.1.mono_dom fun _ hp => hp.large).trans
    ((hpad (-0.063)).mul_right fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl)
      fun p _ => show (p.D₀ : ℝ) ^ (-0.063 : ℝ) * (p.N : ℝ) ^ 2
          = (p.N : ℝ) ^ 2 / (p.D₀ : ℝ) ^ (0.063 : ℝ) by
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        ring
  have hquery := (Corollary26.conclusion.2.comp Sizes.m fun _ _ => trivial).trans (hpad 0.437)
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery (fun _ _ => by positivity)
    fun _ _ => by positivity
  exact ⟨C, hC, fun D₀ N m hN hm hm60 =>
    have hp : Sizes.Corollary26 ⟨D₀, N, m⟩ := ⟨hN, hm, hm60⟩
    ⟨Corollary26.tile_fits hp.large, hboth _ hp⟩⟩

























/-! ### The parameters `c = 21` and `θ = 1/9` of Corollary 31 and Table 2

The sentence before Corollary 26 says: "It is the entry c = 21, q = 0.43 of Table 2". The parameters
of the proof above are those of Corollary 31 at `c = 21`, `θ = 1/9`: this holds for `L`
(`levelsOf_21`), for `γ` and `q` (`Corollary26.gamma_eq` and `Corollary26.q_eq` above), and for `Λ`
(`baseLambda_eq_exp_lnΛ`). The condition `ε < R_c(γ)` holds at `ε = 1/18` (`Corollary26.Rc_digits`),
and `N ≥ D^18` gives the condition `D ≤ N^{0.056}` of the row `c = 21` of the table, which is
`table_2_c21` (`Corollary26.row_condition`). Nothing else rests on this section. -/



























































end ThreeSumApsp

end
end

section


/-!
# Rational parameters for Corollary 31

Corollary 31 has real parameters `c > 10` and `0 < θ < 0.9`, and a real `ε < R_c(γ)` with
`γ = θ ln(1/ρ_c)/ln 4`. A program can only contain rational numbers. This file shows that the
parameters can be replaced by rational ones without loss (`exists_rat_params`): first a rational
`c' > c` so close to `c` that `ε` is still below `R_{c'}(γ)`, by continuity (`continuousAt_Rc`);
then a rational `θ' < θ` so close to `θ` that the exponent `γ` of `c'` and `θ'` is still at least
that of `c` and `θ`. A smaller `θ` makes `q` smaller and `R_{c'}(γ)` larger. The file also writes
the numbers `⌈c m⌉` and `⌈θ m⌉` for rational parameters in integer arithmetic (`levelsOf_div`,
`switchOf_div`).
-/

@[expose] public section

namespace ThreeSumApsp

































































































/-- `t = ⌈θ m⌉` for a rational `θ = p/q`. -/
theorem switchOf_div (p m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    switchOf ((p : ℝ) / q) m = (p * m + q - 1) / q := by
  unfold switchOf
  rw [← Nat.ceilDiv_eq_add_pred_div, ← Nat.ceil_div_eq_ceilDiv (p * m) hq]
  congr 1
  push_cast
  ring

end ThreeSumApsp

end
end

section


/-!
# Corollary 26: the parameters 21, 1/9 and 60, and the regime N ≥ D^18

Corollary 26 is the case c = 21, θ = 1/9 of the programs with rational parameters, with the
threshold 60 (`ratParams26`): the preprocessing calls that of Theorem 30 with L = 21 m and t = ⌈m/9⌉
if m = ⌈log₄ D⌉ ≥ 60. On the inputs with N ≥ D^18, and for m ≥ 60, the hypotheses of Theorem 30 hold
at these L and t (`hyp30_26`), and its two cost expressions are O(N²/D^{0.063}) and O(D^{0.437})
(`costs26`); both come from `Corollary26.costs`. Then the bound N²/D^{0.063} (`preBound26`) and what
is used about it. `regime26` puts this in the form in which the statements about the programs with
rational parameters ask for it (`CostsWithin`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec Finset

/-! ## The parameters -/
















/-- L = 21 m. -/
theorem ratParams26_L (m : ℕ) : ratParams26.L m = 21 * m := by
  simp [RatParams.L, ratParams26]

/-- t = ⌈m/9⌉. -/
theorem ratParams26_t (m : ℕ) : ratParams26.t m = (m + 8) / 9 := by
  simp [RatParams.t, ratParams26]









/-- At the parameters of Corollary 26, Theorem 30 is used with L = 21 m. -/
theorem parOf_ratParams26 (N D₀ : ℕ) : parOf ratParams26 N D₀ = par26 N D₀ := by
  simp only [parOf, par26, ratParams26_L]

/-- At the parameters of Corollary 26, Theorem 30 is used with t = ⌈m/9⌉. -/
theorem switchOf31_ratParams26 (D₀ : ℕ) : switchOf31 ratParams26 D₀ = switch26 D₀ := by
  simp only [switchOf31, switch26, ratParams26_t]

/-- The ceiling ⌈m/9⌉ in natural numbers. -/
theorem switchOf_ninth (m : ℕ) : switchOf (1 / 9) m = (m + 8) / 9 := by
  have h := switchOf_div 1 m (q := 9) (by norm_num)
  norm_num at h
  exact h

/-! ## The two cost expressions -/




/-- **The costs of Theorem 30 at the parameters of Corollary 26**, for m ≥ 60. -/
theorem costs26 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ D₀ N : ℕ, D₀ ^ 18 ≤ N → 60 ≤ logFour D₀ → Hyp30 (par26 N D₀) (switch26 D₀) ∧
      cost8 (21 * logFour D₀) (logFour D₀) (switch26 D₀) N ≤ C * preBound26 D₀ N ∧
      costQuery (21 * logFour D₀) (logFour D₀) (switch26 D₀) ≤ C * (D₀ : ℝ) ^ (0.437 : ℝ) := by
  obtain ⟨C, hC, h⟩ := Corollary26.costs
  refine ⟨C, hC, fun D₀ N hN hm => ?_⟩
  obtain ⟨hN0, hcost8, hquery⟩ := h D₀ N (logFour D₀) hN (ceil_logb_four D₀).symm hm
  rw [switchOf_ninth] at hcost8 hquery
  refine ⟨⟨le_trans (by norm_num) hm, ?_, ?_, hN0⟩, hcost8, hquery⟩
  · change 10 * logFour D₀ ≤ 21 * logFour D₀
    omega
  · change (logFour D₀ + 8) / 9 ≤ logFour D₀
    omega

/-- Proof of Corollary 26: "For m ≥ 60, Theorem 30 thus applies". -/
theorem hyp30_26 {N D₀ : ℕ} (hN : D₀ ^ 18 ≤ N) (hm : 60 ≤ logFour D₀) :
    Hyp30 (par26 N D₀) (switch26 D₀) := by
  obtain ⟨_, -, hcosts⟩ := costs26
  exact (hcosts D₀ N hN hm).1

/-! ## The overheads -/
































/-! ## The regime -/












end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/


















/-! ## The test -/

/-- regimeTest26(N, D) returns 1 if D^18 ≤ N and 0 if not, and changes no cell. -/
theorem regimeTest26_ends {lim : Limits} {P : Program} {d : ℕ} (N D : ℕ) (hD : 1 ≤ D)
    (hword : ((4 * D + N * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Ends lim P d regimeTest26Body ⟨frame [(N : ℤ), (D : ℤ)], μ⟩ 336 fun σ' =>
      σ'.mem = μ ∧ ((σ'.loc 0 = 1 ∧ D ^ 18 ≤ N) ∨ (σ'.loc 0 = 0 ∧ N < D ^ 18)) := by
  unfold regimeTest26Body
  refine Ends.seq 334 2 ((Sec2.regimePow_spec N D hD hword μ _ (by simp) (by simp)).mono le_rfl ?_)
      (by omega)
  rintro ⟨loc', μ'⟩ ⟨em, -, h⟩
  simp only at em h
  exact Ends.set trivial (by simp) ⟨em, by simpa using h⟩

/-- The procedure regimeTest26 returns 1 if D^18 ≤ N and 0 if not, and changes no cell. -/
theorem regimeTest26_meets {lim : Limits} {P : Program} {d : ℕ}
    (hP : P[Proc.regimeTest26]? = some regimeTest26Body)
    (N D : ℕ) (hD : 1 ≤ D) (hword : ((4 * D + N * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Meets lim P Proc.regimeTest26 d [N, D] μ 336 fun r μ' =>
      μ' = μ ∧ ((r = 1 ∧ D ^ 18 ≤ N) ∨ (r = 0 ∧ N < D ^ 18)) :=
  .of_body hP (regimeTest26_ends N D hD hword μ)

/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}

/-- A number that is at most the first part of the need fits in a word. -/
private theorem fits_of_need (ok : (allInstancesNeed26 [N, D₀, w, U]).Ok lim fr d) {n : ℕ}
    (hn : n ≤ 1000 + 100 * D₀ + N * D₀ + D₀ * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5) : (n : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hn) ok.word

/-- The block of Theorem 30, behind the two padded matrices, ends within the cells of the need. -/
private theorem top_le_of_need (hD : 1 ≤ D₀) (H : Hyp30 (par26 N D₀) (switch26 D₀))
    (ok : (allInstancesNeed26 [N, D₀, w, U]).Ok lim fr d) :
    top (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr) ≤ lim.space := by
  have hcells : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have hblock : top (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr) - blockAt N D₀ fr
      ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H (below H) _
  -- each padded matrix has N 4^m ≤ 4 N D₀ cells
  have hpad : N * D (logFour D₀) ≤ 4 * (N * D₀) :=
    (Nat.mul_le_mul_left N (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)).trans_eq (by ring)
  have hbase : blockAt N D₀ fr = fr + 3 + N * D (logFour D₀) + N * D (logFour D₀) := rfl
  omega

/-- If B bounds 10^L, 7^L and 10^m, the three numbers in the limits of Theorem 30 are at most B³ U²,
7 B U and 10 B. -/
private theorem lim30_of_below {p : Sec2.Par} {t b0 B : ℕ} (hB : Below p t B) (std : Std lim)
    (hspace : top p t b0 ≤ lim.space)
    (fits : ∀ n : ℕ, n ≤ B ^ 3 * (U * U) + 7 * (B * U) + 10 * B → (n : ℤ) ≤ lim.word) :
    Lim30 lim p t b0 (U : ℤ) := by
  have hten := hB.T
  have hseven := hB.S7
  have htenm := hB.tenm
  have hvalue : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B ^ 3 * (U * U) :=
    calc 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B * ((B * U) * (B * U)) := by gcongr
      _ = B ^ 3 * (U * U) := by ring
  have henc : 7 ^ (p.L + 1) * U ≤ 7 * (B * U) :=
    calc 7 ^ (p.L + 1) * U = 7 * (7 ^ p.L * U) := by ring
      _ ≤ 7 * (B * U) := by gcongr
  have hpow : 10 ^ (p.L + 1) ≤ 10 * B :=
    calc 10 ^ (p.L + 1) = 10 * 10 ^ p.L := by ring
      _ ≤ 10 * B := by gcongr
  exact {
    std := std
    space := hspace
    value := by exact_mod_cast fits _ (hvalue.trans (by omega))
    enc := by exact_mod_cast fits _ (henc.trans (by omega))
    pow := fits _ (hpow.trans (by omega)) }

/-- In the regime, the need of allInstances26 covers what offline32 asks of the limits. -/
theorem lim31_of_need (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N)
    (ok : (allInstancesNeed26 [N, D₀, w, U]).Ok lim fr d) :
    Lim31 lim ratParams26 N D₀ fr (U : ℤ) := by
  have hcells : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have fits {n : ℕ} := fits_of_need ok (n := n)
  -- 4^m ≤ 4 D₀ and m ≤ 4 D₀
  have h4 : 4 ^ logFour D₀ ≤ 4 * D₀ := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
  have std : Std lim := ⟨ok.space, by exact_mod_cast fits (n := 100) (by omega)⟩
  have large (hm : 60 ≤ logFour D₀) : Lim30 lim (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr)
      (U : ℤ) :=
    have H := hyp30_26 hN hm
    lim30_of_below (B := (N + 1) ^ 5) (below H) std (top_le_of_need hD H ok)
      fun n hn => fits (hn.trans (by omega))
  exact {
    std := std
    space := by
      unfold structEnd
      rw [parOf_ratParams26, switchOf31_ratParams26]
      split_ifs with h
      · omega
      · exact (large (not_lt.mp h)).space
    pow := fits (by omega)
    mword := fits (by change 21 * logFour D₀ + 1 + 1 * logFour D₀ + 9 ≤ _; omega)
    m0word := fits (n := 60) (by omega)
    ip := by exact_mod_cast fits (n := D₀ * (U * U)) (by omega)
    large := fun hm => by rw [parOf_ratParams26, switchOf31_ratParams26]; exact large hm }

end need

/-! ## The matrices of an instance -/







theorem matAt_thinMX {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : MatAt μ x.x
    (thinMX x) := by
  intro i j
  have hlt : (i : ℕ) * x.D + j < x.X.length := by
    rw [h.lenX]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.D)
    have := j.isLt
    omega
  rw [Nat.add_assoc, h.segX.getD hlt 0]
  rfl

theorem matAt_thinMY {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : MatAt μ x.y
    (thinMY x) := by
  intro i j
  have hlt : (i : ℕ) * x.N + j < x.Y.length := by
    rw [h.lenY]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.N)
    have := j.isLt
    omega
  rw [Nat.add_assoc, h.segY.getD hlt 0]
  rfl

/-- The entry of the product of the two matrices is the entry that the task asks for. -/
theorem entryN_thin (x : ThinInst) {I J : ℕ} (hI : I < x.N) (hJ : J < x.N) :
    entryN (thinMX x) (thinMY x) I J = thinEntry x.N x.D x.X x.Y I J := by
  rw [entryN, dif_pos ⟨hI, hJ⟩, Matrix.mul_apply, thinEntry, List.sum_map_range, Finset.sum_range]
  rfl

/-! ## The routine -/

/-- The answers of the offline routine are those that the task asks for. -/
theorem map_entryN_thin {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) :
    (x.WI.zip x.WJ).map (fun q => entryN (thinMX x) (thinMY x) q.1 q.2)
      = thinOut x.N x.D x.X x.Y x.WI x.WJ :=
  List.map_congr_left fun _ hq =>
    entryN_thin x (h.ltWI _ (List.of_mem_zip hq).1) (h.ltWJ _ (List.of_mem_zip hq).2)

/-- **In the regime** the offline routine solves the task. -/
theorem offline32_meets_thinTask {lim : Limits} {P : Program} {c d : ℕ}
    (task : OfflineSpec32 lim P c ratParams26) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hreg : x.D ^ 18 ≤ x.N)
    (ok : (allInstancesNeed26 [x.N, x.D, x.w, x.U]).Ok lim fr d) :
    Meets lim P Proc.offline32 (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32 c ratParams26 x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ' := by
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  have hdepth : d + (84 * x.D + 12) ≤ lim.depth := ok.depth
  have hm4 := logFour_le_four_mul hpre.D_pos
  have spec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) (x.U : ℤ) (x.U : ℤ) μ
    x.WI x.WJ
    { one_le_D := hpre.D_pos, one_le_N := hpre.N_pos
      lim := lim31_of_need hpre.D_pos hreg ok
      absX := fun i j => hpre.leX.abs_getD_le hU0 _
      absY := fun i j => hpre.leY.abs_getD_le hU0 _
      belowX := hpre.belowX, belowY := hpre.belowY }
    { matX := matAt_thinMX hpre, matY := matAt_thinMY hpre
      rows := hpre.segWI, cols := hpre.segWJ
      length_eq := by rw [hpre.lenWI, hpre.lenWJ]
      rows_lt := hpre.ltWI, cols_lt := hpre.ltWJ
      rows_le := by rw [hpre.lenWI]; exact hpre.belowWI
      cols_le := by rw [hpre.lenWI]; exact hpre.belowWJ
      out_le := by rw [hpre.lenWI]; exact hpre.belowOut
      out_matX := by rw [hpre.lenWI]; exact hpre.apartX
      out_matY := by rw [hpre.lenWI]; exact hpre.apartY
      out_rows := by rw [hpre.lenWI]; exact hpre.apartWI
      out_cols := by rw [hpre.lenWI]; exact hpre.apartWJ }
  rw [hpre.lenWI, ratParams26_L, map_entryN_thin hpre] at spec
  exact (spec _ (by omega)).mono le_rfl fun r μ' h => ⟨h.1, fun a ha => h.2 a ha.1 ha.2⟩

/-- **allInstances26 solves the task on all instances**, in every program that holds allInstances26,
regimeTest26 and the brute force at their numbers and in which offline32 satisfies `OfflineSpec32`
at the parameters of Corollary 26, also after more procedures are appended. -/
theorem allInstances26_solves_sourceProof {P : Program} {c : ℕ}
    (hall : P[Proc.allInstances26]? = some allInstances26Body)
    (htest : P[Proc.regimeTest26]? = some regimeTest26Body)
    (hbrute : P[Sec2.pThinBrute]? = some Sec2.thinBruteBody)
    (task : ∀ (R : Program) (lim : Limits), OfflineSpec32 lim (P ++ R) c ratParams26) :
    SolvesN thinTask P Proc.allInstances26 (allInstancesTime26 c) allInstancesNeed26 := by
  refine ⟨allInstances26Body, hall, fun R lim d x μ fr hpre hok => ?_⟩
  have ok : (allInstancesNeed26 [x.N, x.D, x.w, x.U]).Ok lim fr d := hok
  have hword := ok.word
  have hcells := ok.cells
  have hdepth := ok.depth
  simp only [allInstancesNeed26] at hword hcells hdepth
  have hfits : ∀ n : ℕ, n ≤ 1000 + 100 * x.D + x.N * x.D + x.D * (x.U * x.U) → (n : ℤ) ≤ lim.word :=
    fun n hn => le_trans (by exact_mod_cast (by omega)) hword
  have h100 := hfits 100 (by omega)
  have hroom : fr + x.N + 1 ≤ lim.space := by omega
  clear hword hcells
  change Ends lim (P ++ R) d allInstances26Body
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (400 + if x.D ^ 18 ≤ x.N then tOffline32 c ratParams26 x.N x.D x.w
      else 40 * ((x.w + 1) * (x.D + 1))) _
  unfold allInstances26Body
  -- regime := regimeTest26(N, D)
  refine Ends.callToThen (regimeTest26_meets (getElem?_append_of_eq_some htest R) x.N x.D hpre.D_pos
    (hfits _ (by omega)) μ) ?_ (hT := by simp; omega)
  rintro r μ ⟨rfl, hr⟩
  -- if 0 < regime
  refine Ends.iteLast (fun hpos => ?_) (fun hneg => ?_)
  · -- return offline32(N, D, w, U, x, y, wi, wj, out, fr)
    have hreg : x.D ^ 18 ≤ x.N := by
      rcases hr with ⟨-, h⟩ | ⟨rfl, -⟩
      · exact h
      · simp at hpos
    rw [if_pos hreg]
    exact Ends.callTo (offline32_meets_thinTask (task R lim) hpre hreg ok) fun _ _ h => h
  · -- return thinBrute(N, D, w, U, x, y, wi, wj, out, fr)
    have hreg : ¬ x.D ^ 18 ≤ x.N := by
      rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩
      · simp at hneg
      · omega
    rw [if_neg hreg]
    have hbrute : Meets lim (P ++ R) Sec2.pThinBrute (d + 1)
        [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (40 * ((x.w + 1) * (x.D + 1)))
        fun r μ' => thinTask.Post x μ fr r μ' :=
      .of_body (getElem?_append_of_eq_some hbrute R) (Sec2.thinBrute_spec
        ⟨ok.space, by exact_mod_cast h100⟩ x μ fr (x.U : ℤ) hpre hroom (hfits _ (by omega)))
    exact Ends.callTo hbrute fun _ _ h => h

/-! ## The time in the regime -/


















/-! ## The need is polynomial in the parameters -/





section summands

variable {N D U Q : ℕ}














































end summands






















end Light.Sec4

end
end


theorem solution : ∀ {P : Light.Program} {c : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P Light.Sec4.Proc.allInstances26)
      (@Option.some.{0} Light.Stmt Light.Sec4.allInstances26Body) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P Light.Sec4.Proc.regimeTest26)
        (@Option.some.{0} Light.Stmt Light.Sec4.regimeTest26Body) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P Light.Sec2.pThinBrute)
          (@Option.some.{0} Light.Stmt Light.Sec2.thinBruteBody) →
        (∀ (R : Light.Program) (lim : Light.Limits),
            Light.Sec4.OfflineSpec32 lim
              (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
                (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) P R)
              c Light.Sec4.ratParams26) →
          Light.SolvesN Light.thinTask P Light.Sec4.Proc.allInstances26 (Light.Sec4.allInstancesTime26 c)
            Light.Sec4.allInstancesNeed26 := by
  exact @Light.Sec4.allInstances26_solves_sourceProof

#print axioms solution
