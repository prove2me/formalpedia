-- Prove2me | solution 1 for Light.Sec3.ChanHe.frontEnd_contracts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T17:22:32.251674+00:00
-- url     : https://prove2.me/submissions/02712f5d-daff-473c-9c9e-347f8ab5b765

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
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSumSource_CH20Contracts
import Definitions.Def_ThreeSumSource_ReductionClaims
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Init
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
import Mathlib.Algebra.Order.Floor.Semifield
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
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
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
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
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
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_3_3
import Theorems.Thm_Light_Sec3_claim_VW18_Theorem_4_2
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
section
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
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam
section
@[expose] public section
open Filter Asymptotics
namespace ThreeSumApsp
namespace Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
end Dominated
end ThreeSumApsp
end
end
section
public section
open Filter Asymptotics
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
end ThreeSumApsp.WordRam
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
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
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩
attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]
end Light
end
end
section
@[expose] public section
namespace Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc
variable {dst j : ℕ} {f : ℕ → ℤ}
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]
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
end Light
end
end
section
public section
namespace Nat
theorem mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := Nat.add_le_add_left hb _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha
end Nat
namespace Int
end Int
end
end
section
@[expose] public section
namespace List
variable {α β : Type*}
section
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
end
section Sorted
variable [LinearOrder α]
end Sorted
end List
namespace ThreeSumApsp
variable {α β : Type*}
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)
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
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)
theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
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
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h
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
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
namespace ListAt
end ListAt
namespace ArrayAt
end ArrayAt
namespace IndexAt
variable {l : List ℕ} {p : ℕ}
end IndexAt
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
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
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
section rules
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
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
end rules
section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
end
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩
end
section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}
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
@[expose] public section
namespace Light
open ThreeSumApsp.WordRam
end Light
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩
end Light
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace Nat
end Nat
namespace Real
end Real
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Real
end Real
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace IsBigOPow
end IsBigOPow
namespace IsPowPolylog
end IsPowPolylog
end ThreeSumApsp
end
end
section
@[expose] public section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
namespace UpperBigOPow
end UpperBigOPow
namespace UpperPowPolylog
end UpperPowPolylog
namespace UpperPowLittleO
end UpperPowLittleO
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace Scale
variable {α ι : Type*} [Fintype ι] (s : Scale α ι)
variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}
namespace SoftO
variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}
end SoftO
end Scale
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
namespace PolyBounded
variable {F : ℕ → ℕ → ℕ}
end PolyBounded
namespace PolyBounded
end PolyBounded
namespace PolyNeed
variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}
end PolyNeed
end Light
end
end
section
public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
open Real
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace Light.Sec3
end Light.Sec3
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Scan
end Scan
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace PowLt
end PowLt
namespace RootCeil
end RootCeil
end Light.Sec3
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Brute
end Brute
section
variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}
end
end Light.Sec3
end
end
section
public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
namespace HostPoly
variable {D g : ℕ → ℕ}
section parts
variable (hD : PolyBounded fun n _ => D n)
include hD
end parts
end HostPoly
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
namespace CostParams.Hyp
variable {θ : CostParams} (h : θ.Hyp)
include h
end CostParams.Hyp
namespace Steps
variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}
end Steps
section within
variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}
end within
namespace Steps
variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}
end Steps
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
end Light.Sec3
end
end
section
public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
end Light.Sec3
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
end Light
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {d : ℕ}
namespace ChooseHost
end ChooseHost
open ChooseHost
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {d : ℕ}
namespace LopHosts
end LopHosts
open LopHosts
namespace LopArgs
end LopArgs
namespace LopHosts
end LopHosts
open LopHosts
end Light.Sec3
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace PowTable
end PowTable
open PowTable
end Light
end
end
section
@[expose] public section
namespace Light.Sec2
open ThreeSumApsp
namespace Par
end Par
namespace Par
end Par
namespace Par
variable (p : Par)
end Par
end Light.Sec2
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)
end
end ThreeSumApsp.Spec
end
end
section
public section
namespace Light.Sec2
open ThreeSumApsp
variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
end Light.Sec2
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
namespace Dir
end Dir
section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
end
end Light.Sec4
end
end
section
@[expose] public section
open Finset
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
namespace Query31
end Query31
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}
namespace Pre31
end Pre31
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec Finset
namespace IpAt
end IpAt
section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)
variable {X Y}
end
end Light.Sec4
end
end
section
@[expose] public section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
section known
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
end known
section framing
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
end framing
end ThreeSumApsp.WordRam
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}
end
namespace WantedCore
end WantedCore
section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}
end
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}
namespace Offline32
end Offline32
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.WordRam
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.WordRam
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
section need
variable {lim : Limits} {N D₀ w U fr d : ℕ}
end need
section summands
variable {N D U Q : ℕ}
end summands
end Light.Sec4
end
end
section
public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
end Light.Sec4
end
end
section
public section
namespace ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
end ThreeSumApsp.FromClaims
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light.Sec3
end Light.Sec3
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace Theorem19
namespace Choice
variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P
end Choice
end Theorem19
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light.Sec3
end Light.Sec3
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3
open ThreeSumApsp.WordRam ThreeSumApsp.Spec
end Light.Sec3
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light.Sec3
end Light.Sec3
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam
end
end
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace APSPFocusedSource
open ThreeSumApsp.WordRam
end APSPFocusedSource
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR
end
section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}
theorem Ends.callThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨Function.update loc x r, μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                                                            (try have := _root_.Light.Std.const_le (by assumption))
                                                                                            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                                                              ))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by (((first
                                                           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                               first
                                                               | omega
                                                               | (ring_nf; omega))
                                                           | omega
                                                           |
                                                             (simp [] <;>
                                                                 first
                                                                 | omega
                                                                 | (ring_nf; omega))))
                                                               )) :
    Ends lim P d (.call p args x ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.callLast hp h ha hd le_rfl) hT
end
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
section rules
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
theorem Ends.forShape {β : Type} {loc : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt}
    (S : ℕ → β → (ℕ → ℤ) → State) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (s₀ : β) (start : I 0 μ)
    (round : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body (S j s μ') b fun σ' => ∃ s' μ'', σ' = S j s' μ'' ∧ I (j + 1) μ'')
    (done : ∀ (s : β) (μ' : ℕ → ℤ), I n μ' → Q (S n s μ'))
    (first : (⟨Function.update loc i 0, μ⟩ : State) = S 0 s₀ μ := by
      first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (bound : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim (S j s μ') n := by
      intros; ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ))
    (counter : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), (S j s μ').loc i = j := by intros; simp)
    (next : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ),
      (⟨Function.update (S j s μ').loc i ((j : ℤ) + 1), (S j s μ').mem⟩ : State) =
        S (j + 1) s μ' := by
      intros; first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by (((first
                                                             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                   _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                 first
                                                                 | omega
                                                                 | (ring_nf; omega))
                                                             | omega
                                                             |
                                                               (simp [] <;>
                                                                   first
                                                                   | omega
                                                                   | (ring_nf; omega))))
                                                                 )) :
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
@[simp] def updateLocals (loc : ℕ → ℤ) : List (ℕ × ℤ) → ℕ → ℤ
  | [] => loc
  | p :: ps => updateLocals (Function.update loc p.1 p.2) ps
section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
end
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := fun i hi => by
  rw [wrote_done (hl ▸ hi), h i hi]
theorem Ends.pass {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by (((first
                                               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                     _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                   first
                                                   | omega
                                                   | (ring_nf; omega))
                                               | omega
                                               |
                                                 (simp [] <;>
                                                     first
                                                     | omega
                                                     | (ring_nf; omega))))
                                                   )) :
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm
    (fun j μ' hj hμ' => Ends.block ?round le_rfl)
    (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
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
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Copy
end Copy
theorem copy_meets {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by ((((   try refine _root_.Light.SameOn.cell ?_
                                                                      intro macro_local_0 macro_local_1
                                                                      first
                                                                      | (((   repeat
                                                                                ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_2);
                                                                                  (try have := macro_local_2 macro_local_0 (by omega)); revert macro_local_2)
                                                                              intros
                                                                              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                      |
                                                                        (simp [] at macro_local_1;
                                                                          ((  repeat
                                                                                ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_4);
                                                                                  (try have := macro_local_4 macro_local_0 (by omega)); revert macro_local_4)
                                                                              intros
                                                                              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                      | ( ((  repeat
                                                                                ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_6);
                                                                                  (try have := macro_local_6 macro_local_0 (by omega)); revert macro_local_6)
                                                                              intros
                                                                              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *))
                                                                          fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                      its condition K x does not follow from the hypotheses."))))
                                                                        )⟩ hw hdst rfl rfl
    (hT := by ((first
                 | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                       _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                       copyTime]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [copyTime] <;>
                       first
                       | omega
                       | (ring_nf; omega)))
                                  )))
  have hread : wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    wrote_rest (by omega)
  (((  (try have := _root_.Light.Std.space_le (by assumption))
       (try have := _root_.Light.Std.const_le (by assumption))
       simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))
                   )
namespace Fill
end Fill
theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                             (try have := _root_.Light.Std.const_le (by assumption))
                                                             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                               ))
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((((   try refine _root_.Light.SameOn.cell ?_
                                                                                      intro macro_local_0 macro_local_1
                                                                                      first
                                                                                      | (((   repeat
                                                                                                ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_2);
                                                                                                  (try have := macro_local_2 macro_local_0 (by omega)); revert macro_local_2)
                                                                                              intros
                                                                                              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                                      |
                                                                                        (simp [] at macro_local_1;
                                                                                          ((  repeat
                                                                                                ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_4);
                                                                                                  (try have := macro_local_4 macro_local_0 (by omega)); revert macro_local_4)
                                                                                              intros
                                                                                              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                                      | ( ((  repeat
                                                                                                ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_6);
                                                                                                  (try have := macro_local_6 macro_local_0 (by omega)); revert macro_local_6)
                                                                                              intros
                                                                                              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *))
                                                                                          fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))
                                                                                        )⟩
    hw hdst rfl rfl (hT := by ((first
                                 | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                       _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                                       fillTime]
                                     first
                                     | omega
                                     | (ring_nf; omega))
                                 | omega
                                 |
                                   (simp [fillTime] <;>
                                       first
                                       | omega
                                       | (ring_nf; omega)))
                                                  )))
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩
theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                      (try have := _root_.Light.Std.const_le (by assumption))
                                                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                        )) (hs : c.Safe lim σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                                                           (try have := _root_.Light.Std.const_le (by assumption))
                                                                                           simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                                                             )) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩
theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                        (try have := _root_.Light.Std.const_le (by assumption))
                                                        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                          )) (hs : c.Safe lim σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                                                             (try have := _root_.Light.Std.const_le (by assumption))
                                                                                             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                                                               )) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by (((first
                            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                first
                                | omega
                                | (ring_nf; omega))
                            | omega
                            |
                              (simp [] <;>
                                  first
                                  | omega
                                  | (ring_nf; omega))))
                                )) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.next T₁ (h.mono le_rfl rest) hT
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by (((first
                                                                                   | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                         _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                       first
                                                                                       | omega
                                                                                       | (ring_nf; omega))
                                                                                   | omega
                                                                                   |
                                                                                     (simp [] <;>
                                                                                         first
                                                                                         | omega
                                                                                         | (ring_nf; omega))))
                                                                                       )) :
    Ends lim P d s σ T Q :=
  h.mono hT rest
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                           (try have := _root_.Light.Std.const_le (by assumption))
                                           simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                             )) (hT : e.cost + 1 ≤ T := by (((first
                                                                                | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                      _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                    first
                                                                                    | omega
                                                                                    | (ring_nf; omega))
                                                                                | omega
                                                                                |
                                                                                  (simp [] <;>
                                                                                      first
                                                                                      | omega
                                                                                      | (ring_nf; omega))))
                                                                                    )) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      )) (hT : c.cost + 1 ≤ T := by (((first
                                                                         | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                               _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                             first
                                                                             | omega
                                                                             | (ring_nf; omega))
                                                                         | omega
                                                                         |
                                                                           (simp [] <;>
                                                                               first
                                                                               | omega
                                                                               | (ring_nf; omega))))
                                                                             )) :
    Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                      (try have := _root_.Light.Std.const_le (by assumption))
                                                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                        ))
    (hT : c.cost + 1 ≤ T := by (((first
                                    | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                          _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                        first
                                        | omega
                                        | (ring_nf; omega))
                                    | omega
                                    |
                                      (simp [] <;>
                                          first
                                          | omega
                                          | (ring_nf; omega))))
                                        )) : Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod
end Emod
def emodRounds (a M : ℕ) : ℕ := Nat.size (a / M)
@[simp] def emodTime (a M : ℕ) : ℕ := 43 * emodRounds a M + 34
theorem mul_two_pow_le_iff {a M i : ℕ} (hM : 1 ≤ M) : M * 2 ^ i ≤ a ↔ i < emodRounds a M := by
  rw [emodRounds, Nat.lt_size, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
theorem neg_emod_nat (a M : ℕ) (hM : 1 ≤ M) :
    (-(a : ℤ)) % (M : ℤ) = if a % M = 0 then 0 else (M : ℤ) - ((a % M : ℕ) : ℤ) := by
  have h : (a : ℤ) = (M : ℤ) * ((a / M : ℕ) : ℤ) + ((a % M : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a M).symm
  have hlt : a % M < M := Nat.mod_lt _ (by omega)
  split_ifs with h0
  · rw [h0] at h
    rw [h, Nat.cast_zero, add_zero, ← mul_neg]
    exact Int.mul_emod_right _ _
  · have e : -(a : ℤ) = ((M : ℤ) - ((a % M : ℕ) : ℤ)) + (M : ℤ) * (-((a / M : ℕ) : ℤ) - 1) := by
      rw [h]
      push_cast
      ring
    rw [e, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
namespace Emod
structure Pre (lim : Limits) (Mo V fr : ℕ) : Prop where
  mod_pos : 1 ≤ Mo
  space : (lim.space : ℤ) ≤ lim.word
  word : (4 * V + 4 * Mo + 16 : ℤ) ≤ lim.word
  free : fr + (Nat.log 2 (V + 1) + 2) ≤ lim.space
def Table (μ μ' : ℕ → ℤ) (Mo fr i : ℕ) : Prop :=
  (∀ j < i, μ' (fr + j) = ((Mo * 2 ^ j : ℕ) : ℤ)) ∧ Kept μ μ' fr
variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}
theorem table_ends (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Ends lim P d emodTable ⟨frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * emodRounds a Mo + 6) fun σ' =>
      ∃ μ', σ' = ⟨frame [x, Mo, fr, a, emodRounds a Mo, ((Mo * 2 ^ emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
        Table μ μ' Mo fr (emodRounds a Mo) := by
  (((obtain ⟨⟩ := _root_.id F))
              )
  have hK : emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := emodRounds_le haV
  refine Ends.whileConst (fun i σ => ∃ μ',
    σ = ⟨frame [x, Mo, fr, a, i, ((Mo * 2 ^ i : ℕ) : ℤ)], μ'⟩ ∧ Table μ μ' Mo fr i)
    (emodRounds a Mo) emodTableRound.blockCost ?start ?round ?done
    (by simp [emodTableRound]; omega)
  case start => exact ⟨μ, by simp, fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
  case done =>
    rintro _ ⟨μ', rfl, tab⟩
    have hgt : ¬ Mo * 2 ^ emodRounds a Mo ≤ a := fun h =>
      absurd ((mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
    generalize Mo * 2 ^ emodRounds a Mo = t at hgt
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by simp; omega, μ', rfl, tab⟩
  case round =>
    rintro i _ hi ⟨μ', rfl, tab, below⟩
    have hle : Mo * 2 ^ i ≤ a := (mul_two_pow_le_iff F.mod_pos).2 hi
    have hnext : Mo * 2 ^ (i + 1) = Mo * 2 ^ i + Mo * 2 ^ i := by ring
    rw [hnext]
    generalize ht : Mo * 2 ^ i = t at hle
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by simp; omega, ?_⟩
    unfold emodTableRound
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (fr + i) t ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                         )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (t + t : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
    refine ⟨_, rfl, fun j hj => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · rw [Function.update_of_ne (by omega)]
        exact tab j h
      · rw [Function.update_self, ht]
    · rw [Function.update_of_ne (by omega)]
      exact below b hb
theorem reduce_ends (F : Pre lim Mo V fr) (haV : a ≤ V) {μ' : ℕ → ℤ} {t : ℤ}
    (tab : Table μ μ' Mo fr (emodRounds a Mo)) :
    Ends lim P d emodReduce ⟨frame [x, Mo, fr, a, emodRounds a Mo, t], μ'⟩
      (24 * emodRounds a Mo + 4) fun σ' => σ' = ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ := by
  (((obtain ⟨⟩ := _root_.id F))
              )
  have hK : emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := emodRounds_le haV
  have hgt : a < Mo * 2 ^ emodRounds a Mo := not_le.1 fun h =>
    absurd ((mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
  refine Ends.whileConst (fun i σ => ∃ r : ℕ,
    σ = ⟨frame [x, Mo, fr, r, (emodRounds a Mo - i : ℕ), t], μ'⟩ ∧
      r < Mo * 2 ^ (emodRounds a Mo - i) ∧ r % Mo = a % Mo) (emodRounds a Mo)
    emodReduceRound.blockCost ?start ?round ?done (by simp [emodReduceRound]; omega)
  case start => exact ⟨a, by simp, by simpa using hgt, rfl⟩
  case done =>
    rintro _ ⟨r, rfl, hr, hmod⟩
    rw [Nat.sub_self] at hr ⊢
    have hra : r = a % Mo := by rw [← hmod, Nat.mod_eq_of_lt (by simpa using hr)]
    exact ⟨by simp; omega, by simp, by rw [hra]; rfl⟩
  case round =>
    rintro i _ hi ⟨r, rfl, hr, hmod⟩
    obtain ⟨c, hc⟩ : ∃ c, emodRounds a Mo - i = c + 1 := ⟨emodRounds a Mo - i - 1, by omega⟩
    rw [show emodRounds a Mo - (i + 1) = c by omega]
    rw [hc] at hr ⊢
    have hcell : μ' (fr + c) = ((Mo * 2 ^ c : ℕ) : ℤ) := tab.1 c (by omega)
    have hle : Mo * 2 ^ c ≤ a := (mul_two_pow_le_iff F.mod_pos).2 (by omega)
    have hsub : ∀ r' : ℕ, Mo * 2 ^ c ≤ r' → (r' - Mo * 2 ^ c) % Mo = r' % Mo :=
      fun r' h => Nat.sub_mul_mod h
    rw [show Mo * 2 ^ (c + 1) = Mo * 2 ^ c + Mo * 2 ^ c by ring] at hr
    generalize Mo * 2 ^ c = m at hr hcell hle hsub ⊢
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    unfold emodReduceRound
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (c : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                    )
    refine Ends.iteLast (fun h => ?_) (fun h => ?_)
    · have hmr : m ≤ r := by
        simp [hcell] at h
        omega
      exact Ends.setTo (r - m : ℕ) ⟨r - m, rfl, by omega, by rw [hsub r hmr, hmod]⟩
        (by (((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcell] <;> omega))
                             ))
    · have hrm : r < m := by
        simp [hcell] at h
        omega
      exact Ends.skip ⟨r, rfl, hrm, hmod⟩
theorem sign_ends (F : Pre lim Mo V fr) (hax : (a : ℤ) = |x|) {μ' : ℕ → ℤ} {t : ℤ} :
    Ends lim P d emodSign ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ 12 fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ σ'.mem = μ' := by
  have hword := F.word
  have hr : a % Mo < Mo := Nat.mod_lt _ F.mod_pos
  generalize hrem : a % Mo = r at hr
  refine Ends.iteLast (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    have hmod := neg_emod_nat a Mo F.mod_pos
    rw [hrem, show -(a : ℤ) = x by rw [hax, abs_of_neg hneg]; ring] at hmod
    refine Ends.iteLast (fun hz => ?_) (fun hz => ?_)
    · have hz : r = 0 := by simpa using hz
      exact Ends.setTo 0 ⟨by rw [hmod, if_pos hz]; rfl, rfl⟩
    · have hz : ¬ r = 0 := by simpa using hz
      exact Ends.setTo ((Mo : ℤ) - r) ⟨by rw [hmod, if_neg hz]; rfl, rfl⟩
  · have hpos : 0 ≤ x := by simpa using hpos
    refine Ends.setTo (r : ℤ) ⟨?_, rfl⟩
    rw [← abs_of_nonneg hpos, ← hax, ← hrem]
    exact (Int.natCast_mod a Mo)
theorem _root_.Light.emod_meets {p : ℕ} (hp : P[p]? = some emodBody) (F : Pre lim Mo V fr)
    (hx : |x| ≤ (V : ℤ)) :
    Meets lim P p d [x, Mo, fr] μ (emodTime x.natAbs Mo) fun r μ' =>
      r = x % (Mo : ℤ) ∧ Kept μ μ' fr := by
  have hword := F.word
  have hax : ((x.natAbs : ℕ) : ℤ) = |x| := Int.natCast_natAbs x
  have haV : x.natAbs ≤ V := by omega
  refine .of_body hp ?_
  unfold emodTime
  generalize x.natAbs = a at hax haV ⊢
  have tail : Ends lim P d (.set Count (k 0) ;; .set Mult (v Modulus) ;; emodTable ;;
      emodReduce ;; emodSign) ⟨frame [x, Mo, fr, a], μ⟩ (43 * emodRounds a Mo + 26) fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ Kept μ σ'.mem fr := by
    refine Ends.setToThen (0 : ℕ) (Ends.setToThen (Mo : ℕ) ?_)
    refine Ends.next _ ((table_ends F haV).mono le_rfl ?_)
    rintro _ ⟨μ', rfl, tab⟩
    refine Ends.next _ ((reduce_ends F haV tab).mono le_rfl ?_)
    rintro _ rfl
    exact (sign_ends F hax).mono (by (((first
                                          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                              first
                                              | omega
                                              | (ring_nf; omega))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | (ring_nf; omega))))
                                              )) fun σ' h =>
      ⟨h.1, fun b hb => by rw [h.2]; exact tab.2 b hb⟩
  refine Ends.iteThen (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    rw [abs_of_neg hneg] at hax
    exact Ends.setToThen (a : ℕ) (tail.mono (by (((first
                                                     | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                           _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                         first
                                                         | omega
                                                         | (ring_nf; omega))
                                                     | omega
                                                     |
                                                       (simp [] <;>
                                                           first
                                                           | omega
                                                           | (ring_nf; omega))))
                                                         )) fun _ h => h)
  · have hpos : 0 ≤ x := by simpa using hpos
    rw [abs_of_nonneg hpos] at hax
    exact Ends.setToThen (a : ℕ) (tail.mono (by (((first
                                                     | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                           _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                         first
                                                         | omega
                                                         | (ring_nf; omega))
                                                     | omega
                                                     |
                                                       (simp [] <;>
                                                           first
                                                           | omega
                                                           | (ring_nf; omega))))
                                                         )) fun _ h => h)
end Emod
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Logs
end Logs
open Logs
@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12
theorem log2_meets {p x : ℕ} (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  refine .of_body hp ?_
  unfold log2Body log2Time
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             2
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ (i + 1) : ℕ)], μ⟩)
    (Nat.log 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hi
    have hle : 2 ^ (i + 1) ≤ x :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_log_le_self 2 hx)
    have hix : i < x := lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
      ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hle)
    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]
    generalize 2 ^ (i + 1) = q at hle
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                   (try have := _root_.Light.Std.const_le (by assumption))
                                                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                     ), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ (Nat.log 2 x + 1) = q at hlt
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (Nat.log 2 x) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                          )
    exact ⟨rfl, rfl⟩
@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10
theorem clog2_meets {p x : ℕ} (hp : P[p]? = some clog2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (clog2Time x) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ := by
  have hle : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  refine .of_body hp ?_
  unfold clog2Body clog2Time
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             1
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ i : ℕ)], μ⟩)
    (Nat.clog 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : 2 ^ i < x := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hix : i < x := lt_trans (Nat.lt_pow_self (by norm_num)) hlt
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]
    generalize 2 ^ i = q at hlt
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                   (try have := _root_.Light.Std.const_le (by assumption))
                                                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                     ), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ Nat.clog 2 x = q at hle
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (Nat.clog 2 x) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                           )
    exact ⟨rfl, rfl⟩
@[simp] def halfTime (h : ℕ) : ℕ := 10 * ((h + 1) / 2) + 10
theorem half_meets {p h : ℕ} (hp : P[p]? = some halfBody) (μ : ℕ → ℤ)
    (hword : ((h + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [h] μ (halfTime h) fun r μ' => r = (((h + 1) / 2 : ℕ) : ℤ) ∧ μ' = μ := by
  refine .of_body hp ?_
  unfold halfBody halfTime
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             0
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [h, i], μ⟩) ((h + 1) / 2) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                   (try have := _root_.Light.Std.const_le (by assumption))
                                                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                     ), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen ((h + 1) / 2 : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                              )
    exact ⟨rfl, rfl⟩
end Light
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']
theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((((   try refine _root_.Light.SameOn.cell ?_
                                                                                    intro macro_local_0 macro_local_1
                                                                                    first
                                                                                    | (((   repeat
                                                                                              ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_2);
                                                                                                (try have := macro_local_2 macro_local_0 (by omega)); revert macro_local_2)
                                                                                            intros
                                                                                            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                                    |
                                                                                      (simp [] at macro_local_1;
                                                                                        ((  repeat
                                                                                              ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_4);
                                                                                                (try have := macro_local_4 macro_local_0 (by omega)); revert macro_local_4)
                                                                                            intros
                                                                                            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                                                    | ( ((  repeat
                                                                                              ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_6);
                                                                                                (try have := macro_local_6 macro_local_0 (by omega)); revert macro_local_6)
                                                                                            intros
                                                                                            try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *))
                                                                                        fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                    its condition K x does not follow from the hypotheses."))))
                                                                                      )) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩
theorem Seg.update_in (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (x : ℤ) :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  intro j hj
  have hj' : j < l.length := by simpa using hj
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne (by omega), List.getElem_set_of_ne (by omega), h j hj']
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc
theorem SameOutside2.refl {m : ℕ} : SameOutside2 μ μ a n b m := SameOn.refl
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by ((((   try refine _root_.Light.SameOn.cell ?_
                                                       intro macro_local_0 macro_local_1
                                                       first
                                                       | (((   repeat
                                                                 ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_2);
                                                                   (try have := macro_local_2 macro_local_0 (by omega)); revert macro_local_2)
                                                               intros
                                                               try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                       |
                                                         (simp [] at macro_local_1;
                                                           ((  repeat
                                                                 ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_4);
                                                                   (try have := macro_local_4 macro_local_0 (by omega)); revert macro_local_4)
                                                               intros
                                                               try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)); omega)
                                                       | ( ((  repeat
                                                                 ((with_reducible rename _root_.Light.SameOn _ _ _ => macro_local_6);
                                                                   (try have := macro_local_6 macro_local_0 (by omega)); revert macro_local_6)
                                                               intros
                                                               try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *))
                                                           fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                       its condition K x does not follow from the hypotheses."))))
                                                         )) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simpa using hd)
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Merge
variable {l r : List ℤ} {i j : ℕ}
theorem step_left (hi : i < l.length) (hj : j < r.length) (h : l[i] ≤ r[j]) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [h]
theorem step_right (hi : i < l.length) (hj : j < r.length) (h : r[j] < l[i]) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [not_le.2 h]
theorem step_left_end (hi : i < l.length) (hj : r.length ≤ j) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_nil_of_le hj, List.merge_right, List.merge_right, List.drop_eq_getElem_cons hi]
theorem step_right_end (hi : l.length ≤ i) (hj : j < r.length) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_nil_of_le hi, List.nil_merge, List.nil_merge, List.drop_eq_getElem_cons hj]
end Merge
namespace Merge
end Merge
namespace Merge
structure Pre (lim : Limits) (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  segL : Seg μ a l
  segR : Seg μ b r
  spaceL : a + l.length ≤ lim.space
  spaceR : b + r.length ≤ lim.space
  spaceD : dst + (l.length + r.length) ≤ lim.space
  sepL : Apart a l.length dst (l.length + r.length)
  sepR : Apart b r.length dst (l.length + r.length)
def Inv (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (out : List ℤ), σ = ⟨frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r
def Taken (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ i j, i + j = t ∧ Inv μ a b dst l r i j σ
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}
theorem takeLeft (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hi : i < l.length)
    (hm : (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j)) :
    mergeTakeLeft.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, -, hj, same, hlen, seg, hout⟩ := h
  (((obtain ⟨⟩ := _root_.id C))
              )
  have hread : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get hi)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                  (try have := _root_.Light.Std.const_le (by assumption))
                  simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, mergeTakeLeft] <;> omega))
                                      ), i + 1, j, by omega,
    Function.update μ' (dst + out.length) l[i], out ++ [l[i]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by simp only [List.length_append, List.length_singleton]; omega,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeLeft, update_frame_setLocal, haddr, hread]
theorem takeRight (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hj : j < r.length)
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, hi, -, same, hlen, seg, hout⟩ := h
  (((obtain ⟨⟩ := _root_.id C))
              )
  have hread : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get hj)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                  (try have := _root_.Light.Std.const_le (by assumption))
                  simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, mergeTakeRight] <;> omega))
                                       ), i, j + 1, by omega,
    Function.update μ' (dst + out.length) r[j], out ++ [r[j]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by simp only [List.length_append, List.length_singleton]; omega,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeRight, update_frame_setLocal, haddr, hread]
@[simp] def _root_.Light.mergeTime (n : ℕ) : ℕ := 40 * n + 12
theorem _root_.Light.merge_meets {p : ℕ} (hp : P[p]? = some mergeBody)
    (C : Pre lim μ a b dst l r) :
    Meets lim P p d [a, l.length, b, r.length, dst] μ (mergeTime (l.length + r.length)) fun _ μ' =>
      Seg μ' dst (l.merge r) ∧ SameOutside μ μ' dst (l.length + r.length) := by
  (((obtain ⟨⟩ := _root_.id C))
              )
  refine .of_body hp ?_
  unfold mergeTime
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  refine Ends.whileBlock (Taken μ a b dst l r) (l.length + r.length) ?start ?round ?done
    (by simp [mergeTakeLeft, mergeTakeRight]; omega)
  case start =>
    exact ⟨0, 0, rfl, μ, [], rfl, Nat.zero_le _, Nat.zero_le _, .refl, rfl, Seg.nil, by simp⟩
  case done =>
    rintro _ ⟨i, j, hij, μ', out, rfl, hi, hj, same, hlen, seg, hout⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)] at hout
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by simp; omega, by simpa [← hout] using seg, same⟩
  case round =>
    rintro _ σ ht ⟨i, j, rfl, hI⟩
    have left := takeLeft C hI
    have right := takeRight C hI
    obtain ⟨μ', out, rfl, hi, hj, same, -⟩ := hI
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by simp; omega, ?_⟩
    by_cases c1 : i < l.length
    · refine .ite_pos ?_
      by_cases c2 : j < r.length
      · have hreadL : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get c1)
        have hreadR : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get c2)
        refine .ite_pos ?_
        by_cases c3 : r[j] < l[i]
        · exact .ite_pos (right c2 (step_right c1 c2 c3)) (by simpa [hreadL, hreadR] using c3)
        · exact .ite_neg (left c1 (step_left c1 c2 (not_lt.1 c3)))
            (by simpa [hreadL, hreadR] using c3)
      · exact .ite_neg (left c1 (step_left_end c1 (by omega)))
    · exact .ite_neg (right (by omega) (step_right_end (by omega) (by omega)))
end Merge
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program}
namespace MergeSort
end MergeSort
def sortTime (n : ℕ) : ℕ := 61 * (n * Nat.clog 2 n) + 74 * (n - 1) + 4
namespace MergeSort
theorem clog_split {n : ℕ} (hn : 2 ≤ n) :
    (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2) + n
      ≤ n * Nat.clog 2 n := by
  have h1 : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
  have h2 : Nat.clog 2 (n - (n + 1) / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  have hh : (n + 1) / 2 ≤ n := by omega
  rw [h1]
  generalize (n + 1) / 2 = h at *
  generalize Nat.clog 2 h = c at *
  have a1 : (n - h) * Nat.clog 2 (n - h) ≤ (n - h) * c := Nat.mul_le_mul_left _ h2
  have a2 : h * c + (n - h) * c = n * c := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have a3 : n * (c + 1) = n * c + n := by ring
  omega
theorem time_split {n : ℕ} (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by
  have := clog_split hn
  unfold sortTime
  omega
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    KeptBut μ μ' fr a L.length
theorem sorted_refl {μ : ℕ → ℤ} {a fr : ℕ} {L : List ℤ} (hseg : Seg μ a L) (hL : L.length ≤ 1) :
    Sorted μ a fr L μ := by
  refine ⟨⟨L, hseg, .refl _, ?_⟩, .refl⟩
  match L, hL with
  | [], _ => exact .nil
  | [x], _ => exact List.pairwise_singleton _ _
theorem sorted_merge {μ μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} {a fr h m : ℕ} {L S₁ S₂ : List ℤ} (hh : h ≤ L.length)
    (hP₁ : S₁.Perm (L.take h)) (hO₁ : S₁.Pairwise (· ≤ ·))
    (hk₁ : KeptBut μ μ₁ fr a (L.take h).length) (hP₂ : S₂.Perm (L.drop h))
    (hO₂ : S₂.Pairwise (· ≤ ·)) (hk₂ : KeptBut μ₁ μ₂ fr (a + h) (L.drop h).length)
    (hk₃ : SameOutside μ₂ μ₃ fr m) (hS₄ : Seg μ₄ a (S₁.merge S₂))
    (hk₄ : SameOutside μ₃ μ₄ a L.length) : Sorted μ a fr L μ₄ := by
  refine ⟨⟨S₁.merge S₂, hS₄, ?_, hO₁.merge hO₂⟩, fun c hc => ?_⟩
  · calc (S₁.merge S₂).Perm (S₁ ++ S₂) := List.merge_perm_append _
      _ |>.Perm (L.take h ++ L.drop h) := hP₁.append hP₂
      _ = L := List.take_append_drop h L
  · have hl₁ : (L.take h).length = h := by simp; omega
    have hl₂ : (L.drop h).length = L.length - h := by simp
    have := hc.2
    rw [hk₄ c hc.2, hk₃ c (Or.inl hc.1), hk₂ c ⟨hc.1, by omega⟩, hk₁ c ⟨hc.1, by omega⟩]
variable {pSort pHalf pMerge pCopy : ℕ}
theorem join_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) {d a fr h n : ℕ} {r : ℤ} {S₁ S₂ : List ℤ} {μ : ℕ → ℤ}
    (hl₁ : S₁.length = h) (hl₂ : S₂.length = n - h) (hh : h ≤ n) (hn : 1 ≤ n) (hS₁ : Seg μ a S₁)
    (hS₂ : Seg μ (a + h) S₂) (haf : a + n ≤ fr) (hfr : fr + n ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (sortJoin pMerge pCopy) ⟨frame [n, a, fr, h, r], μ⟩ (56 * n + 34) fun σ' =>
      ∃ μ' : ℕ → ℤ, SameOutside μ μ' fr n ∧ Seg σ'.mem a (S₁.merge S₂) ∧
        SameOutside μ' σ'.mem a n := by
  have hlm : (S₁.merge S₂).length = n := by rw [List.length_merge]; omega
  have hmerge := merge_meets (d := d + 1) C.merge (a := a) (b := a + h) (dst := fr) (l := S₁)
    (r := S₂) ⟨hw, hS₁, hS₂, by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  rw [hl₁, hl₂, show h + (n - h) = n by omega] at hmerge
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         | refine _root_.Light.Ends.callToThen (hmerge _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen hmerge ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁
               ⟨hseg, hk₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                        )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega) (by omega) (by omega))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega) (by omega) (by omega))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨hcopy, hk₂⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                     )
  exact ⟨μ₁, hk₁, fun i hi => (hcopy i (by omega)).trans (hseg i hi), hk₂⟩
theorem body_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {d a fr : ℕ} {L : List ℤ}
    {μ : ℕ → ℤ} (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space)
    (hd : d < lim.depth)
    (ih : ∀ (a' : ℕ) (L' : List ℤ) (μ' : ℕ → ℤ), 1 < L.length → 2 * L'.length ≤ L.length + 1 →
      Seg μ' a' L' → a' + L'.length ≤ fr →
      Meets lim P pSort (d + 1) [L'.length, a', fr] μ' (sortTime L'.length) fun _ =>
        Sorted μ' a' fr L') :
    Ends lim P d (sortBody pSort pHalf pMerge pCopy) ⟨frame [L.length, a, fr], μ⟩
      (sortTime L.length) fun σ' => Sorted μ a fr L σ'.mem := by
  refine Ends.iteLast (fun hc => ?_) (fun hc => Ends.skip (sorted_refl hseg (by simpa using hc)))
    (hT := by simp [sortTime])
  have hn : 1 < L.length := by simpa using hc
  have htime := time_split hn
  have hhalf := half_meets (d := d + 1) C.half μ (h := L.length)
    (le_trans (by exact_mod_cast (by omega : L.length + 1 ≤ lim.space)) hw)
  have hlt : (L.length + 1) / 2 < L.length := by omega
  have hpos : 1 ≤ (L.length + 1) / 2 := by omega
  have htwice : 2 * ((L.length + 1) / 2) ≤ L.length + 1 := by omega
  have htwice' : L.length ≤ 2 * ((L.length + 1) / 2) := by omega
  generalize (L.length + 1) / 2 = h at *
  have hl₁ : (L.take h).length = h := by simp; omega
  have hl₂ : (L.drop h).length = L.length - h := by simp
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         | refine _root_.Light.Ends.callToThen (hhalf _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen hhalf ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₀ ⟨rfl, hμ₀⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                      )
  obtain rfl : μ = μ₀ := hμ₀.symm
  have hsort₁ := ih a (L.take h) μ hn (by omega) (hseg.take h) (by omega)
  rw [hl₁] at hsort₁
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         | refine _root_.Light.Ends.callToThen (hsort₁ _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen hsort₁ ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨⟨S₁, hS₁, hP₁, hO₁⟩, hk₁⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                       )
  have hseg₂ : Seg μ₁ (a + h) (L.drop h) :=
    (hseg.drop h).congr fun i hi => hk₁ _ ⟨by omega, Or.inr (by omega)⟩
  have hsort₂ := ih (a + h) (L.drop h) μ₁ hn (by omega) hseg₂ (by omega)
  rw [hl₂] at hsort₂
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         | refine _root_.Light.Ends.callToThen (hsort₂ _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen hsort₂ ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨⟨S₂, hS₂, hP₂, hO₂⟩, hk₂⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                       )
  have hlS₁ := hP₁.length_eq
  have hS₁' : Seg μ₂ a S₁ := hS₁.congr fun i hi => hk₂ _ ⟨by omega, Or.inl (by omega)⟩
  refine (join_ends C hw (hP₁.length_eq.trans hl₁) (hP₂.length_eq.trans hl₂) hlt.le hn.le hS₁' hS₂
    haf hfr hd).mono (by (((first
                              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                  first
                                  | omega
                                  | (ring_nf; omega))
                              | omega
                              |
                                (simp [] <;>
                                    first
                                    | omega
                                    | (ring_nf; omega))))
                                  )) ?_
  rintro _ ⟨μ₃, hk₃, hS₄, hk₄⟩
  exact sorted_merge hlt.le hP₁ hO₁ hk₁ hP₂ hO₂ hk₂ hk₃ hS₄ hk₄
theorem _root_.Light.sort_meets (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      Meets lim P pSort d [L.length, a, fr] μ (sortTime L.length) fun _ => Sorted μ a fr L := by
  induction hn : L.length using Nat.strong_induction_on generalizing a L μ with
  | _ n ih =>
    subst hn
    intro d hd
    refine Meets.of_body C.sort (body_ends C hw h1 hseg haf hfr (by omega)
      fun a' L' μ' hn hhalf hseg' haf' =>
        ih L'.length (by omega) hseg' haf' (by omega) rfl (d + 1) ?_)
    have hclog : Nat.clog 2 L.length = Nat.clog 2 ((L.length + 1) / 2) + 1 := by
      simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
    have := Nat.clog_mono_right 2 (by omega : L'.length ≤ (L.length + 1) / 2)
    omega
end MergeSort
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Sieve
theorem primesBelow_two : primesBelow 2 = [] := by decide
theorem primesBelow_one : primesBelow 1 = [] := by decide
theorem primesBelow_succ_of_prime {c : ℕ} (h : c.Prime) :
    primesBelow (c + 1) = primesBelow c ++ [c] := by
  simp [primesBelow, List.range_succ, List.filter_append, h]
theorem primesBelow_succ_of_not_prime {c : ℕ} (h : ¬ c.Prime) :
    primesBelow (c + 1) = primesBelow c := by
  simp [primesBelow, List.range_succ, List.filter_append, h]
theorem length_primesBelow_add_two_le {i : ℕ} (hi : 2 ≤ i) : (primesBelow i).length + 2 ≤ i := by
  induction i, hi using Nat.le_induction with
  | base => simp [primesBelow_two]
  | succ i _ ih =>
    by_cases h : i.Prime
    · rw [primesBelow_succ_of_prime h]
      simpa using ih
    · rw [primesBelow_succ_of_not_prime h]
      omega
theorem sort_primesLE (m : ℕ) : (Nat.primesLE m).sort (· ≤ ·) = primesBelow (m + 1) := by
  refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _) ?_ ?_
  · exact (List.pairwise_le_range).filter _
  · refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (List.nodup_range.filter _)).2
      fun q => ?_
    simp [Nat.mem_primesLE]
theorem length_primesBelow (m : ℕ) : (primesBelow (m + 1)).length = (Nat.primesLE m).card := by
  rw [← sort_primesLE, Finset.length_sort]
theorem not_marked_two (j : ℕ) : ¬ Marked 2 j := by
  rintro ⟨p, hp, h2, -, -⟩
  exact absurd hp.two_le (by omega)
theorem prime_iff_not_marked {i : ℕ} (hi : 2 ≤ i) : i.Prime ↔ ¬ Marked i i := by
  constructor
  · rintro h ⟨p, hp, hlt, hdvd, -⟩
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp h).1 hdvd) (by omega)
  · intro h
    by_contra hn
    have hlt := (Nat.not_prime_iff_minFac_lt hi).1 hn
    exact h ⟨i.minFac, Nat.minFac_prime (by omega), hlt, Nat.minFac_dvd i, hlt⟩
theorem marked_succ_of_not_prime {i : ℕ} (h : ¬ i.Prime) (j : ℕ) :
    Marked (i + 1) j ↔ Marked i j := by
  constructor
  · rintro ⟨p, hp, hlt, h1, h2⟩
    have : p ≠ i := by
      rintro rfl
      exact h hp
    exact ⟨p, hp, by omega, h1, h2⟩
  · rintro ⟨p, hp, hlt, h1, h2⟩
    exact ⟨p, hp, by omega, h1, h2⟩
theorem marked_succ_of_prime {i : ℕ} (h : i.Prime) (j : ℕ) :
    Marked (i + 1) j ↔ Marked i j ∨ (i ∣ j ∧ i < j) := by
  constructor
  · rintro ⟨p, hp, hlt, h1, h2⟩
    by_cases hpi : p = i
    · subst hpi
      exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨p, hp, by omega, h1, h2⟩
  · rintro (⟨p, hp, hlt, h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨p, hp, by omega, h1, h2⟩
    · exact ⟨i, h, by omega, h1, h2⟩
theorem sum_div_pow_le (m k : ℕ) : ∑ r ∈ Finset.range (2 ^ k - 1), m / (r + 1) ≤ k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
      have := Nat.one_le_two_pow (n := k)
      rw [pow_succ]
      omega
    rw [h2, Finset.sum_range_add]
    have hblock : ∑ x ∈ Finset.range (2 ^ k), m / (2 ^ k - 1 + x + 1) ≤ m := by
      calc ∑ x ∈ Finset.range (2 ^ k), m / (2 ^ k - 1 + x + 1)
          ≤ ∑ _x ∈ Finset.range (2 ^ k), m / 2 ^ k := by
            refine Finset.sum_le_sum fun x _ => Nat.div_le_div_left ?_ (by positivity)
            have := Nat.one_le_two_pow (n := k)
            omega
        _ = 2 ^ k * (m / 2 ^ k) := by simp
        _ ≤ m := Nat.mul_div_le m _
    have : (k + 1) * m = k * m + m := by ring
    omega
theorem sum_div_le (m : ℕ) : ∑ r ∈ Finset.range (m - 1), m / (r + 2) ≤ (Nat.log 2 m + 1) * m := by
  have h1 : ∑ r ∈ Finset.range (m - 1), m / (r + 2)
      ≤ ∑ r ∈ Finset.range (m - 1 + 1), m / (r + 1) := by
    rw [Finset.sum_range_succ']
    exact Nat.le_add_right _ _
  have h2 : ∑ r ∈ Finset.range (m - 1 + 1), m / (r + 1)
      ≤ ∑ r ∈ Finset.range (2 ^ (Nat.log 2 m + 1) - 1), m / (r + 1) := by
    refine Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 ?_)
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    have h3 : 2 ≤ 2 ^ (Nat.log 2 m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.log 2 m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [Nat.succ_eq_add_one] at this
    omega
  exact h1.trans (h2.trans (sum_div_pow_le m _))
variable {μ : ℕ → ℤ} {m out fr : ℕ}
theorem time_le (m : ℕ) : 15 * m + 23 + 4 + loopTime m + 2 ≤ sieveTime m := by
  have hsum := sum_div_le m
  have hmul : 15 * m * (Nat.log 2 m + 5) = 15 * ((Nat.log 2 m + 1) * m) + 60 * m := by ring
  simp only [loopTime, sieveTime, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum]
  omega
theorem clear_ends (pre : Pre lim m out fr) :
    Ends lim P d clear ⟨frame [m, out, fr], μ⟩ (15 * m + 23) (Cleared μ m out fr (m + 1)) := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  refine Ends.whileBlock (Cleared μ m out fr) (m + 1) ?start ?round ?done
  case start => exact ⟨μ, rfl, fun i hi => absurd hi (by omega), .refl⟩
  case done =>
    rintro _ ⟨μ', rfl, hzero, same⟩
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), μ', rfl, hzero, same⟩
  case round =>
    rintro j _ hj ⟨μ', rfl, hzero, same⟩
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                    (try have := _root_.Light.Std.const_le (by assumption))
                                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                      ), Function.update μ' (fr + j) 0, ?_, ?_,
      same.update ⟨by omega, by omega⟩ _⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases h : i = j
      · simp [h]
      · rw [Function.update_of_ne (by omega)]
        exact hzero i (by omega)
theorem lt_add_iff_of_dvd {i j J : ℕ} (hJ : i ∣ J) (hj : i ∣ j) (hne : j ≠ J) : j < J + i ↔ j < J :=
  ⟨fun h => lt_of_le_of_ne (Nat.le_of_lt_add_of_dvd h hj hJ) hne, fun h => by omega⟩
theorem mark_round {i cnt J : ℕ} {σ : State} (pre : Pre lim m out fr) (hi : 1 ≤ i) (hJ : i ∣ J)
    (hiJ : i < J) (hJm : J ≤ m) (h : Marking μ m out fr i cnt J σ) :
    (Stmt.store (v Table +' v Mult) (k 1) ;; .set Mult (v Mult +' v Cand)).Runs lim σ
      (Marking μ m out fr i cnt (J + i)) := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  obtain ⟨μ', rfl, htab, same⟩ := h
  refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                    (try have := _root_.Light.Std.const_le (by assumption))
                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                      ), Function.update μ' (fr + J) 1, by simp [update_frame_setLocal], ?_,
    same.update ⟨by omega, by omega⟩ _⟩
  intro j hj
  by_cases hjJ : j = J
  · subst hjJ
    rw [Function.update_self, if_pos ⟨hJ, hiJ, by omega⟩]
  · rw [Function.update_of_ne (by omega), htab j hj]
    by_cases hdvd : i ∣ j
    · simp only [hdvd, true_and, lt_add_iff_of_dvd hJ hdvd hjJ]
    · simp only [hdvd, false_and]
theorem mark_ends {i cnt : ℕ} (pre : Pre lim m out fr) (hi : 1 ≤ i) (him : i ≤ m) :
    Ends lim P d mark ⟨frame [m, out, fr, i, (2 * i : ℕ), cnt], μ⟩ (15 * (m / i) + 6) fun σ' =>
      ∃ J, m < J ∧ Marking μ m out fr i cnt J σ' := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  have hq : 1 ≤ m / i := (Nat.le_div_iff_mul_le hi).2 (by omega)
  refine Ends.whileBlock (fun t => Marking μ m out fr i cnt ((t + 2) * i)) (m / i - 1) ?start ?round
    ?done (by (((first
                   | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                         _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                       first
                       | omega
                       | (ring_nf; omega))
                   | omega
                   |
                     (simp [] <;>
                         first
                         | omega
                         | (ring_nf; omega))))
                       ))
  case start =>
    refine ⟨μ, by simp, fun j _ => (if_neg ?_).symm, .refl⟩
    rintro ⟨hdvd, hlt, hlt2⟩
    exact absurd (Nat.le_of_lt_add_of_dvd (by omega : j < i + i) hdvd dvd_rfl) (by omega)
  case done =>
    rintro _ h
    have hgt : m < (m / i - 1 + 2) * i := by
      rw [show m / i - 1 + 2 = m / i + 1 by omega]
      exact (Nat.div_lt_iff_lt_mul hi).1 (Nat.lt_succ_self _)
    generalize (m / i - 1 + 2) * i = J at h hgt
    obtain ⟨μ', rfl, -⟩ := id h
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), J, hgt, h⟩
  case round =>
    rintro t σ ht h
    have hle : (t + 2) * i ≤ m := (Nat.le_div_iff_mul_le hi).1 (by omega)
    have hlt : i < (t + 2) * i :=
      lt_of_lt_of_le (by omega : i < 2 * i) (Nat.mul_le_mul_right i (by omega))
    have hrun := mark_round pre hi (Dvd.intro_left _ rfl) hlt hle h
    rw [show (t + 2) * i + i = (t + 1 + 2) * i by ring] at hrun
    generalize (t + 2) * i = J at h hle
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), hrun⟩
theorem take_ends {i : ℕ} {σ : State} (pre : Pre lim m out fr) (him : i ≤ m) (hprime : i.Prime)
    (h : Sieved μ m out fr i i σ) :
    Ends lim P d take σ (15 * (m / i) + 19) (Sieved μ m out fr i (i + 1)) := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  obtain ⟨μ', J, rfl, seg, htab, kept⟩ := h
  have hcnt := length_primesBelow_add_two_le hprime.two_le
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (out + (primesBelow i).length) i ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                             )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             ((primesBelow i).length + 1 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                           )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (2 * i : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                      )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (mark_ends pre hprime.one_le him) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (mark_ends pre hprime.one_le him) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨J', hJ', μ'', rfl, htab', same⟩))
                                                                                      )
  rw [Sieved, primesBelow_succ_of_prime hprime]
  refine ⟨μ'', J', by simp,
    (seg.snoc i).keep (SameOn.mono same fun b hb => Or.inl (by simp at hb; omega)), fun j hj => ?_,
    (kept.write (by omega) _).then same fun b hb => ⟨hb, hb.2⟩⟩
  rw [htab' j hj, Function.update_of_ne (by omega), marked_succ_of_prime hprime]
  by_cases hmul : i ∣ j ∧ i < j
  · simp [hmul, show j < J' by omega]
  · have : ¬ (i ∣ j ∧ i < j ∧ j < J') := fun hc => hmul ⟨hc.1, hc.2.1⟩
    rw [if_neg this, htab j hj]
    tauto
theorem next_ends {i T : ℕ} {σ : State} (pre : Pre lim m out fr) (him : i ≤ m)
    (h : Sieved μ m out fr i (i + 1) σ) (hT : 4 ≤ T) :
    Ends lim P d (.set Cand (v Cand +' k 1)) σ T (Sieved μ m out fr (i + 1) (i + 1)) := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  obtain ⟨μ', J, rfl, hrest⟩ := h
  exact Ends.setTo (i + 1 : ℕ) ⟨μ', J, rfl, hrest⟩
theorem round_ends {i : ℕ} {σ : State} (pre : Pre lim m out fr) (hi : 2 ≤ i) (him : i ≤ m)
    (h : Sieved μ m out fr i i σ) :
    Ends lim P d round σ (15 * (m / i) + 30) (Sieved μ m out fr (i + 1) (i + 1)) := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  have htake := fun hprime => take_ends (P := P) (d := d) pre him hprime h
  obtain ⟨μ', J, rfl, seg, htab, kept⟩ := h
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · have hzero : μ' (fr + i) = 0 := by simpa using hc
    have hprime : i.Prime := (prime_iff_not_marked hi).2 ((htab i him).1 hzero)
    exact Ends.next _
      ((htake hprime).mono le_rfl fun _ h' => next_ends pre him h' (by (((first
                                                                            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                first
                                                                                | omega
                                                                                | (ring_nf; omega))
                                                                            | omega
                                                                            |
                                                                              (simp [] <;>
                                                                                  first
                                                                                  | omega
                                                                                  | (ring_nf; omega))))
                                                                                )))
  · have hzero : μ' (fr + i) ≠ 0 := by simpa using hc
    have hprime : ¬ i.Prime := fun hp => hzero ((htab i him).2 ((prime_iff_not_marked hi).1 hp))
    refine Ends.next 0 (Ends.skip (next_ends pre him ?_ (by (((first
                                                                 | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                       _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                     first
                                                                     | omega
                                                                     | (ring_nf; omega))
                                                                 | omega
                                                                 |
                                                                   (simp [] <;>
                                                                       first
                                                                       | omega
                                                                       | (ring_nf; omega))))
                                                                     ))))
    rw [Sieved, primesBelow_succ_of_not_prime hprime]
    exact ⟨μ', J, rfl, seg,
      fun j hj => (htab j hj).trans (marked_succ_of_not_prime hprime j).not.symm, kept⟩
theorem _root_.Light.sieve_meets {p : ℕ} (hp : P[p]? = some sieveBody) (pre : Pre lim m out fr) :
    Meets lim P p d [m, out, fr] μ (sieveTime m) fun r μ' =>
      r = ((Nat.primesLE m).card : ℤ) ∧ SegN μ' out ((Nat.primesLE m).sort (· ≤ ·)) ∧
        SameOutside2 μ μ' out m fr (m + 1) := by
  (((obtain ⟨⟩ := _root_.id pre))
                )
  have htime := time_le m
  refine .of_body hp ?_
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (clear_ends pre) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (clear_ends pre) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨μ₁, rfl, hzero, same⟩
                 ))
                                                           )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (2 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  refine Ends.next (loopTime m) ((Ends.while (fun r => Sieved μ m out fr (r + 2) (r + 2)) (m - 1)
    (fun r => 15 * (m / (r + 2)) + 30) ?start ?round ?done).mono (le_of_eq (by simp [loopTime]))
    fun _ h => h)
  case start =>
    rw [Sieved, primesBelow_two]
    exact ⟨μ₁, 0, rfl, Seg.nil, fun j hj => by simp [hzero j (by omega), not_marked_two],
      SameOn.mono same fun b hb => hb.2⟩
  case round =>
    rintro r σ hr h
    have hrun := round_ends (P := P) (d := d) pre (by omega) (by omega : r + 2 ≤ m) h
    obtain ⟨μ', J, rfl, -⟩ := h
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), hrun⟩
  case done =>
    rintro _ ⟨μ', J, rfl, seg, -, kept⟩
    have hlist : primesBelow (m - 1 + 2) = primesBelow (m + 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [primesBelow_two, primesBelow_one]
      · rw [show m - 1 + 2 = m + 1 by omega]
    rw [hlist] at seg
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    ((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen ((primesBelow (m + 1)).length : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                   _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                   hlist]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hlist] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlist] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                                           )
    refine ⟨?_, ?_, kept⟩
    · simp [length_primesBelow]
    · rw [sort_primesLE]
      exact seg
end Sieve
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Sqrt
end Sqrt
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
  have hlt : K < (Nat.sqrt K + 1) * (Nat.sqrt K + 1) := Nat.lt_succ_sqrt K
  have hself : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
  refine .of_body hp ?_
  unfold sqrtBody sqrtTime
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             1
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) (Nat.sqrt K) (by simp) ?round ?done
    le_rfl)
  case round =>
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                   (try have := _root_.Light.Std.const_le (by assumption))
                                                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                     ), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (Nat.sqrt K) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                         )
    exact ⟨rfl, rfl⟩
end Light
end
end
section
@[expose] public section
namespace Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)
variable {dst j : ℕ} {f : ℕ → ℤ}
end Light
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
section distinct
variable {U : ℕ} {S : Finset ℤ}
end distinct
section positions
variable {n : ℕ} {x : Fin n → ℤ}
end positions
section oneArray
variable {N W : ℕ} {X Y Z : ℕ → ℤ}
end oneArray
section node
variable {n U : ℕ} {ν : Node}
end node
section inputs
variable {n U : ℕ} {x : Fin n → ℤ}
theorem card_image_univ_le (x : Fin n → ℤ) : #(univ.image x) ≤ n :=
  card_image_le.trans_eq (card_fin n)
end inputs
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace List
variable {α β : Type*}
theorem take_succ_getD (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_add_one, List.getD_eq_getElem l d hi, List.getElem?_eq_getElem hi,
    Option.toList_some]
section
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
end
theorem count_take_succ [DecidableEq α] (l : List α) (x : α) {i : ℕ}
    (hi : i < l.length) :
    (l.take (i + 1)).count x = (l.take i).count x + if l[i] = x then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi, List.count_append, List.count_singleton]
  simp
theorem count_take_succ_getD [DecidableEq α] (l : List α) (x : α) {i : ℕ} (hi : i < l.length)
    (d : α) :
    (l.take (i + 1)).count x = (l.take i).count x + if l.getD i d = x then 1 else 0 := by
  rw [List.count_take_succ l x hi, List.getD_eq_getElem l d hi]
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
theorem count_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = (Finset.univ.filter fun i => f i = a).card := by
  simpa [List.take_of_length_le] using count_take_ofFn f a n
section Sorted
variable [LinearOrder α]
theorem getD_notMem_take_of_sorted {l : List α} (hs : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length)
    (d : α) (h : i = 0 ∨ l.getD i d ≠ l.getD (i - 1) d) : l.getD i d ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hsame⟩ := List.mem_iff_getElem.1 hm
  have hji : j < i := (List.length_take_le i l).trans_lt' hj
  rcases h with rfl | hne
  · omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (show i - 1 < l.length by omega)] at hne
  rw [List.getElem_take, List.getD_eq_getElem _ _ hi] at hsame
  have hpred : l[i - 1] ≤ l[i] := List.pairwise_iff_getElem.1 hs _ _ _ _ (by omega)
  have hle : l[j] ≤ l[i - 1] := by
    rcases Nat.lt_or_ge j (i - 1) with hlt | hge
    · exact List.pairwise_iff_getElem.1 hs _ _ _ _ hlt
    · exact le_of_eq (by congr 1; omega)
  exact hne (le_antisymm (hsame ▸ hle) hpred)
end Sorted
end List
namespace ThreeSumApsp
variable {α β : Type*}
theorem AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  h _ (List.getElem_mem hi)
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
def bitRow (Λ z : ℕ) : List ℤ := (List.range Λ).map fun β => if z.testBit β then 1 else 0
@[simp] theorem length_bitRow (Λ z : ℕ) : (bitRow Λ z).length = Λ := by simp [bitRow]
theorem bitTable_cons (V Λ : ℕ) (x : ℤ) (L : List ℤ) :
    bitTable V Λ (x :: L) = bitRow Λ (lab V x) ++ bitTable V Λ L := by
  simp [bitTable, bitRow]
theorem bitTable_append (V Λ : ℕ) (L : List ℤ) (x : ℤ) :
    bitTable V Λ (L ++ [x]) = bitTable V Λ L ++ bitRow Λ (lab V x) := by
  simp [bitTable, bitRow, List.flatMap_append]
theorem length_bitTable (V Λ : ℕ) (L : List ℤ) : (bitTable V Λ L).length = L.length * Λ := by
  induction L with
  | nil => simp [bitTable]
  | cons x L ih =>
    rw [bitTable_cons, List.length_append, ih, length_bitRow, List.length_cons, Nat.succ_mul,
      Nat.add_comm]
theorem eq_ofFn_vecOf {n : ℕ} {X : List ℤ} (hX : X.length = n) : X = List.ofFn (vecOf n X) := by
  refine List.ext_getElem (by simp [hX]) fun i h1 h2 => ?_
  simp [vecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
theorem toFinset_eq_image {n : ℕ} {X : List ℤ} (hX : X.length = n) :
    X.toFinset = univ.image (vecOf n X) := by
  conv_lhs => rw [eq_ofFn_vecOf hX]
  ext a
  simp [List.mem_ofFn]
theorem count_eq_card {n : ℕ} {X : List ℤ} (hX : X.length = n) (a : ℤ) :
    X.count a = #{i : Fin n | vecOf n X i = a} := by
  conv_lhs => rw [eq_ofFn_vecOf hX]
  exact List.count_ofFn _ a
theorem Values.of_perm {n : ℕ} {X Ls D : List ℤ} (hX : X.length = n) (hp : Ls.Perm X)
    (hD : D.Nodup) (hv : D.toFinset = Ls.toFinset) :
    Values n X D (D.map fun a => (Ls.count a : ℤ)) :=
  ⟨hD, by rw [hv, List.toFinset_eq_of_perm _ _ hp, toFinset_eq_image hX],
    List.map_congr_left fun a _ => by rw [hp.count_eq, count_eq_card hX]⟩
theorem Values.length_le {n : ℕ} {X D C : List ℤ} (h : Values n X D C) : D.length ≤ n := by
  rw [← List.toFinset_card_of_nodup h.nodup, h.values]
  exact card_image_univ_le _
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace ThreeSumApsp
theorem prefR_start {L : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z < 2 ^ L) : prefR L L z = z := by
  simp [prefR, Int.emod_eq_of_lt h0 h]
theorem pref_step {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (z : ℤ) :
    prefQ ℓ z = shiftQ (2 ^ L) (prefQ (ℓ + 1) z) (prefR L (ℓ + 1) z) ∧
      prefR L ℓ z = shiftR (2 ^ L) (prefR L (ℓ + 1) z) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [prefQ, prefR, shiftQ, shiftR, Nat.add_sub_cancel_left,
    show ℓ + 1 + j - ℓ = j + 1 by omega]
  rw [show (2 : ℤ) ^ (ℓ + 1 + j) = 2 * 2 ^ ℓ * 2 ^ j by ring,
    show (2 : ℤ) ^ (ℓ + 1) = 2 * 2 ^ ℓ by ring, show (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j by ring]
  have hm : (0 : ℤ) < 2 ^ ℓ := by positivity
  have hs : (0 : ℤ) < 2 ^ j := by positivity
  generalize (2 : ℤ) ^ ℓ = m at hm
  generalize (2 : ℤ) ^ j = s at hs
  have hz := Int.mul_ediv_add_emod z (2 * m)
  have hb0 := Int.emod_nonneg z (show 2 * m ≠ 0 by omega)
  have hb2 := Int.emod_lt_of_pos z (show 0 < 2 * m by omega)
  generalize z / (2 * m) = a at hz
  generalize z % (2 * m) = b at hz hb0 hb2
  by_cases hb : b < m
  · have hcond : 2 * (b * s) < 2 * m * s := by linarith [mul_pos (sub_pos.2 hb) hs]
    obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique hm (a := z) (q := 2 * a) (r := b)).2
      ⟨by linarith, hb0, hb⟩
    rw [if_pos hcond, if_pos hcond, hq, hr]
    exact ⟨rfl, by ring⟩
  · have hcond : ¬ 2 * (b * s) < 2 * m * s := by
      linarith [mul_nonneg (sub_nonneg.2 (not_lt.1 hb)) hs.le]
    obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique hm (a := z) (q := 2 * a + 1) (r := b - m)).2
      ⟨by linarith, by omega, by omega⟩
    rw [if_neg hcond, if_neg hcond, hq, hr]
    exact ⟨rfl, by ring⟩
theorem prefR_nonneg (L ℓ : ℕ) (z : ℤ) : 0 ≤ prefR L ℓ z :=
  mul_nonneg (Int.emod_nonneg _ (by positivity)) (by positivity)
theorem prefR_lt {L ℓ : ℕ} (h : ℓ ≤ L) (z : ℤ) : prefR L ℓ z < 2 ^ L := by
  have hmod : z % 2 ^ ℓ < 2 ^ ℓ := Int.emod_lt_of_pos _ (by positivity)
  rw [prefR, ← Nat.add_sub_cancel' h, pow_add, Nat.add_sub_cancel' h]
  exact mul_lt_mul_of_pos_right hmod (by positivity)
theorem prefQ_natCast (ℓ z : ℕ) : prefQ ℓ (z : ℤ) = ((z / 2 ^ ℓ : ℕ) : ℤ) := by
  simp [prefQ]
theorem testBit_iff_shift {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (z : ℕ) :
    z.testBit ℓ = true ↔ ¬ 2 * prefR L (ℓ + 1) (z : ℤ) < 2 ^ L := by
  have hstep := (pref_step h (z : ℤ)).1
  rw [prefQ_natCast, prefQ_natCast, shiftQ] at hstep
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  split_ifs at hstep with hc
  · exact iff_of_false (by omega) (not_not.2 hc)
  · exact iff_of_true (by omega) hc
end ThreeSumApsp
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.Spec ThreeSumApsp.ChanHe
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Pick
end Pick
structure DigitsFrom (μ μ' : ℕ → ℤ) (row Λ z ℓ : ℕ) : Prop where
  digits : ∀ β, ℓ ≤ β → β < Λ → μ' (row + β) = if z.testBit β then 1 else 0
  same : SameOutside μ μ' row Λ
theorem DigitsFrom.write {μ μ' : ℕ → ℤ} {row Λ z ℓ : ℕ} (h : DigitsFrom μ μ' row Λ z (ℓ + 1))
    (hℓ : ℓ < Λ) {b : ℤ} (hb : b = if z.testBit ℓ then 1 else 0) :
    DigitsFrom μ (Function.update μ' (row + ℓ) b) row Λ z ℓ := by
  refine ⟨fun β h₁ h₂ => ?_, h.same.write (by omega) _⟩
  by_cases hβ : β = ℓ
  · rw [hβ, Function.update_self, hb]
  · rw [Function.update_of_ne (by omega)]
    exact h.digits β (by omega) h₂
theorem DigitsFrom.seg {μ μ' : ℕ → ℤ} {row Λ z : ℕ} (h : DigitsFrom μ μ' row Λ z 0) :
    Seg μ' row (bitRow Λ z) := fun β hβ => by
  simp only [bitRow, List.getElem_map, List.getElem_range]
  exact h.digits β (Nat.zero_le β) (by simpa [bitRow] using hβ)
namespace Bits
end Bits
def BitsPowInv (μ : ℕ → ℤ) (len s V bt fr : ℤ) (Λ j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [len, s, V, Λ, bt, fr, 0, 2 ^ j, 0, 0, 0, j], μ⟩
theorem bitsPow_ends {μ : ℕ → ℤ} {len s V bt fr : ℤ} {Λ B : ℕ} (hB : 2 ^ Λ ≤ B)
    (hword : (B : ℤ) ≤ lim.word) :
    Ends lim P d bitsPow ⟨frame [len, s, V, Λ, bt, fr], μ⟩ (12 * Λ + 8)
      (· = ⟨frame [len, s, V, Λ, bt, fr, 0, 2 ^ Λ, 0, 0, 0, Λ], μ⟩) := by
  have hB1 : (1 : ℤ) ≤ B := by exact_mod_cast Nat.one_le_two_pow.trans hB
  unfold bitsPow
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  refine Ends.whileBlock (BitsPowInv μ len s V bt fr Λ) Λ ?start ?round ?done
  case start => simp [BitsPowInv]
  case round =>
    rintro j _ hj rfl
    have hpow : 2 ^ (j + 1) ≤ B := (Nat.pow_le_pow_right (by norm_num) hj).trans hB
    have hpow' : (2 : ℤ) ^ j * 2 ≤ B := by exact_mod_cast hpow
    have hj' : ((j + 1 : ℕ) : ℤ) ≤ B := by exact_mod_cast Nat.lt_two_pow_self.le.trans hpow
    have : (0 : ℤ) < 2 ^ j := by positivity
    push_cast at hj'
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                                   (try have := _root_.Light.Std.const_le (by assumption))
                                                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                                     ),
      by simp [BitsPowInv, update_frame_setLocal, pow_succ, mul_comm]⟩
  case done =>
    rintro _ rfl
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), rfl⟩
def BitsRowInv (μ : ℕ → ℤ) (len s V bt fr idx : ℤ) (row Λ z : ℕ) (t : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (ℓ cur : ℕ), ℓ + t = Λ ∧ cur = row + ℓ ∧
    σ = ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, cur, prefR Λ ℓ z, Λ], μ'⟩ ∧
    DigitsFrom μ μ' row Λ z ℓ
theorem bitsRow_ends {μ : ℕ → ℤ} {len s V bt fr idx : ℤ} {row Λ z B : ℕ} (hz : z < 2 ^ Λ)
    (hB : 2 ^ Λ ≤ B) (hword : ((2 * B + 2 : ℕ) : ℤ) ≤ lim.word) (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row + Λ ≤ lim.space) :
    Ends lim P d bitsRow
      ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, ((row + Λ : ℕ) : ℤ), z, Λ], μ⟩ (23 * Λ + 4)
      fun σ' => ∃ μ',
        σ' = ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, row, prefR Λ 0 z, Λ], μ'⟩ ∧
        Seg μ' row (bitRow Λ z) ∧ SameOutside μ μ' row Λ := by
  have hB' : (2 : ℤ) ^ Λ ≤ B := by exact_mod_cast hB
  push_cast at hword
  unfold bitsRow
  refine Ends.whileBlock (BitsRowInv μ len s V bt fr idx row Λ z) Λ ?start ?round ?done
    (by simp; omega)
  case start =>
    exact ⟨μ, Λ, row + Λ, rfl, rfl, by rw [prefR_start (by positivity) (by exact_mod_cast hz)],
      fun β h₁ h₂ => absurd h₂ (by omega), .refl⟩
  case round =>
    rintro t _ ht ⟨μ', ℓ', cur, hℓ, hcur, rfl, hdig⟩
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, ℓ' = ℓ + 1 := ⟨ℓ' - 1, by omega⟩
    have hfits := prefR_nonneg Λ (ℓ + 1) (z : ℤ)
    have hfits' := prefR_lt (show ℓ + 1 ≤ Λ by omega) (z : ℤ)
    have hstep := (pref_step (show ℓ + 1 ≤ Λ by omega) (z : ℤ)).2
    have hbit := testBit_iff_shift (show ℓ + 1 ≤ Λ by omega) z
    generalize prefR Λ (ℓ + 1) (z : ℤ) = r at hfits hfits' hstep hbit
    have hpred : ((cur - 1 : ℕ) : ℤ) = (cur : ℤ) - 1 := by omega
    have haddr : ((cur : ℤ) - 1).toNat = row + ℓ := by omega
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    by_cases hc : 2 * r < 2 ^ Λ
    ·
      exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc] <;> omega))
                              ), _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 0) (by omega) (by rw [if_neg fun h => hbit.1 h hc])⟩
    ·
      exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc] <;> omega))
                              ), _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 1) (by omega) (by rw [if_pos (hbit.2 hc)])⟩
  case done =>
    rintro _ ⟨μ', ℓ, cur, hℓ, hcur, rfl, hdig⟩
    obtain rfl : ℓ = 0 := by omega
    obtain rfl : cur = row := by omega
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), μ', rfl, hdig.seg, hdig.same⟩
def BitsInv (μ : ℕ → ℤ) (s V Λ bt fr : ℕ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (row : ℕ) (cur rest : ℤ), row = bt + i * Λ ∧
    σ = ⟨frame [L.length, s, V, Λ, bt, fr, i, 2 ^ Λ, row, cur, rest, Λ], μ'⟩ ∧
    Seg μ' bt (bitTable V Λ (L.take i)) ∧ SameOutside μ μ' bt (L.length * Λ)
theorem bitsElem_ends {μ : ℕ → ℤ} {s V Λ bt fr i : ℕ} {L : List ℤ}
    (C : Bits.Ctx lim μ s V Λ bt L) (hi : i < L.length) {σ : State}
    (hI : BitsInv μ s V Λ bt fr L i σ) :
    Ends lim P d bitsElem σ (23 * Λ + 19) fun σ' => σ'.loc Bits.Idx = i ∧
      BitsInv μ s V Λ bt fr L (i + 1)
        { σ' with loc := Function.update σ'.loc Bits.Idx ((i : ℤ) + 1) } := by
  obtain ⟨μ', row, cur, rest, hrow, rfl, hseg, hsame⟩ := hI
  have hw := C.space_le
  (((obtain ⟨⟩ := _root_.id C))
              )
  have hrows : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  have hnext : row + Λ = bt + (i + 1) * Λ := by rw [hrow, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have hread : μ' (s + i) = L.getD i 0 := (hsame _ (by omega)).trans (C.seg.getD hi 0)
  have hfits := abs_le.1 (C.bounded.getElem hi)
  rw [← List.getD_eq_getElem _ 0 hi, ← hread] at hfits
  obtain ⟨z, hz⟩ : ∃ z, z = lab V (L.getD i 0) := ⟨_, rfl⟩
  have hlab : (z : ℤ) = μ' (s + i) + V := by
    rw [hz, ← hread]
    exact Int.toNat_of_nonneg (by omega)
  unfold bitsElem
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen z ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (row + Λ : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (bitsRow_ends (lim := lim) (z := z) (B := 4 * V + 4) (by omega) C.pow_le
                 (by push_cast; omega) hw (by omega))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (bitsRow_ends (lim := lim) (z := z) (B := 4 * V + 4) (by omega) C.pow_le
                 (by push_cast; omega) hw (by omega))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨μ'', rfl, hrowSeg, hrowSame⟩
                 ))
                                                                            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (row + Λ : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  refine ⟨by simp, μ'', row + Λ, row, prefR Λ 0 z, hnext,
    by simp [update_frame_setLocal], ?_, hsame.trans (hrowSame.mono (by omega) (by omega))⟩
  have hlen : (bitTable V Λ (L.take i)).length = i * Λ := by
    rw [length_bitTable, List.length_take, min_eq_left hi.le]
  rw [List.take_succ_getD L hi 0, bitTable_append, seg_append, hlen, ← hrow, ← hz]
  exact ⟨hseg.keep, hrowSeg⟩
theorem bits_spec {p : ℕ} (hP : P[p]? = some bitsBody) : BitsSpec lim P p := by
  intro d fr s bt V Λ L μ C
  (((obtain ⟨⟩ := _root_.id C))
              )
  refine Meets.of_body hP ?_
  unfold tBits bitsBody
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (bitsPow_ends (lim := lim) (B := 4 * V + 4) C.pow_le (by push_cast; omega)) ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (bitsPow_ends (lim := lim) (B := 4 * V + 4) C.pow_le (by push_cast; omega)) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ rfl))
                                    )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen bt ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
             )
  have htime := Nat.mul_le_mul_left L.length (show 1 + (23 * Λ + 19) + 7 ≤ 60 * Λ + 40 by omega)
  refine Ends.for (BitsInv μ s V Λ bt fr L) L.length (23 * Λ + 19) ?start ?round ?done ?bound
    (hT := by simp only [Expr.cost]; omega)
  case start =>
    exact ⟨μ, bt, 0, 0, by simp, by simp [update_frame_setLocal], by simp [bitTable], .refl⟩
  case round => exact fun i σ hi _ hI => bitsElem_ends C hi hI
  case bound =>
    rintro i _ - - ⟨μ', row, cur, rest, -, rfl, -⟩
    ((((   (try have := _root_.Light.Std.space_le (by assumption))
           (try have := _root_.Light.Std.const_le (by assumption))
           simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
             )
  case done =>
    rintro _ - ⟨μ', row, cur, rest, -, rfl, hseg, hsame⟩
    rw [List.take_length] at hseg
    exact ⟨hseg, hsame⟩
end Light.Sec3.ChanHe
end
end
section
public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
theorem natCast_dvd_sub_iff_emod_eq (M : ℕ) (x y : ℤ) :
    (M : ℤ) ∣ x - y ↔ x % (M : ℤ) = y % (M : ℤ) :=
  Int.modEq_iff_dvd.symm.trans eq_comm
theorem coll_le_sq (S : Finset ℤ) (M : ℕ) : coll S M ≤ #S ^ 2 :=
  calc coll S M ≤ #S.offDiag := card_filter_le _ _
    _ = #S * #S - #S := offDiag_card S
    _ ≤ #S ^ 2 := by rw [sq]; omega
theorem coll_eq_sum (S : Finset ℤ) (M : ℕ) :
    coll S M = ∑ x ∈ S, (#(bucket S M (x % (M : ℤ))) - 1) := by
  have hfiber : ∀ x ∈ S,
      #(bucket S M (x % (M : ℤ))) - 1 = #{y ∈ S | x ≠ y ∧ (M : ℤ) ∣ x - y} := by
    intro x hx
    rw [← card_erase_of_mem (show x ∈ bucket S M (x % (M : ℤ)) from mem_filter.mpr ⟨hx, rfl⟩)]
    congr 1
    ext y
    simp only [bucket, mem_filter, mem_erase, natCast_dvd_sub_iff_emod_eq, ne_comm (a := x),
      eq_comm (a := x % _)]
    tauto
  have hpairs : {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2} =
      {p ∈ S ×ˢ S | p.1 ≠ p.2 ∧ (M : ℤ) ∣ p.1 - p.2} := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_product, and_assoc]
  rw [sum_congr rfl hfiber, coll, hpairs, card_filter, sum_product]
  simp only [card_filter]
section searches
variable {Q : Finset ℕ} {U : ℕ} {S₁ S₂ S₃ : Finset ℤ}
end searches
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
section cells
variable {S : Finset ℤ} {M U : ℕ}
theorem heavy_subset (S : Finset ℤ) (M : ℕ) : heavy S M ⊆ S := filter_subset _ _
end cells
theorem height_pos (n : ℕ) : 1 ≤ height n :=
  Nat.clog_pos (b := 2) (n := Nat.log 2 n + 2) (by norm_num) (by omega)
namespace Replaced
variable {n U j : ℕ} {T : Finset ℤ}
end Replaced
end ChanHe
end ThreeSumApsp
end
end
section
public section
namespace Nat
end Nat
namespace Int
theorem natCast_toNat_emod {M : ℕ} (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (Int.natCast_ne_zero_iff_pos.2 hM))
end Int
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec.ChanHeArray
open ChanHe Finset
def keys (M : ℕ) (L : List ℤ) : List ℕ := L.map fun x => (x % (M : ℤ)).toNat
@[simp] theorem length_keys (M : ℕ) (L : List ℤ) : (keys M L).length = L.length := by simp [keys]
theorem keys_lt {M : ℕ} (hM : 1 ≤ M) (L : List ℤ) : ∀ r ∈ keys M L, r < M := by
  intro r hr
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
  exact Int.toNat_emod_lt hM x
theorem map_cast_keys {M : ℕ} (hM : 1 ≤ M) (L : List ℤ) :
    (keys M L).map (fun r : ℕ => (r : ℤ)) = L.map fun x => x % (M : ℤ) := by
  rw [keys, List.map_map]
  exact List.map_congr_left fun x _ => Int.natCast_toNat_emod hM x
theorem card_bucket {M : ℕ} (hM : 1 ≤ M) {L : List ℤ} (hL : L.Nodup) (r : ℕ) :
    #(bucket L.toFinset M r) = (keys M L).count r := by
  have hfilter : bucket L.toFinset M (r : ℤ) =
      (L.filter fun x => decide (x % (M : ℤ) = (r : ℤ))).toFinset := by
    ext x
    simp [bucket]
  rw [hfilter, List.toFinset_card_of_nodup (hL.filter _), keys, List.count_eq_countP,
    List.countP_map, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr fun x _ => ?_
  have hcast := Int.natCast_toNat_emod hM x
  change decide (x % (M : ℤ) = (r : ℤ)) = decide ((x % (M : ℤ)).toNat = r)
  exact decide_eq_decide.2 (by omega)
theorem arr_of_count_eq_one {M : ℕ} (hM : 1 ≤ M) {L : List ℤ} (hL : L.Nodup) (pd : ℤ) {j : ℕ}
    (hj : j < L.length) (hc : (keys M L).count (L[j] % (M : ℤ)).toNat = 1) :
    arr L.toFinset M pd (L[j] % (M : ℤ)).toNat = L[j] := by
  rw [arr, card_bucket hM hL, if_pos hc]
  rw [← card_bucket hM hL] at hc
  obtain ⟨a, ha⟩ := card_eq_one.1 hc
  have hmem : L[j] ∈ bucket L.toFinset M ((L[j] % (M : ℤ)).toNat : ℕ) := by
    rw [bucket, mem_filter, List.mem_toFinset]
    exact ⟨List.getElem_mem hj, (Int.natCast_toNat_emod hM _).symm⟩
  rw [ha] at hmem ⊢
  rw [sum_singleton, mem_singleton.1 hmem]
theorem arr_of_count_ne_one {M : ℕ} (hM : 1 ≤ M) {L : List ℤ} (hL : L.Nodup) (pd : ℤ) {r : ℕ}
    (hc : (keys M L).count r ≠ 1) : arr L.toFinset M pd r = pd := by
  rw [arr, card_bucket hM hL, if_neg hc]
theorem arr_of_le {M : ℕ} (hM : 1 ≤ M) (S : Finset ℤ) (pd : ℤ) {i : ℕ} (hi : M ≤ i) :
    arr S M pd i = pd := by
  have hempty : bucket S M i = ∅ := by
    rw [bucket, filter_eq_empty_iff]
    intro x _ hx
    have hlt : x % (M : ℤ) < M := Int.emod_lt_of_pos _ (by exact_mod_cast hM)
    omega
  rw [arr, hempty, if_neg (by simp)]
theorem oneArray_cells (ν : Node) (V i : ℕ) :
    ν.oneArray V (4 * i) = 10 * (6 * V + 4) ∧
      ν.oneArray V (4 * i + 1) = arr ν.S₁ ν.M (2 * V + 1) i + (6 * V + 4) ∧
      ν.oneArray V (4 * i + 2) = arr ν.S₂ ν.M (2 * V + 1) i + 3 * (6 * V + 4) ∧
      ν.oneArray V (4 * i + 3) = arrZ ν.S₃ ν.M V i + 4 * (6 * V + 4) := by
  have hcell : ∀ r < 4, (4 * i + r) % 4 = r ∧ (4 * i + r) / 4 = i := fun r hr => by omega
  have hzero : 4 * i % 4 = 0 := Nat.mul_mod_right 4 i
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Node.oneArray, ChanHe.oneArray, arrXY, pad, hzero, hcell 1 (by norm_num),
      hcell 2 (by norm_num), hcell 3 (by norm_num)] <;> norm_num <;> ring
end ThreeSumApsp.Spec.ChanHeArray
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
section Filter
variable {α β : Type}
def passList (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) : List β := ((Z.take i).filter p).map f
@[simp] theorem passList_zero (p : α → Bool) (f : α → β) (Z : List α) : passList p f Z 0 = [] := by
  simp [passList]
theorem passList_length (p : α → Bool) (f : α → β) (Z : List α) :
    passList p f Z Z.length = (Z.filter p).map f := by
  simp [passList]
theorem passList_succ_of {p : α → Bool} (f : α → β) {Z : List α} {i : ℕ} (hi : i < Z.length)
    (h : p Z[i] = true) : passList p f Z (i + 1) = passList p f Z i ++ [f Z[i]] := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, List.map_append]
  simp [h]
theorem passList_succ_of_not {p : α → Bool} (f : α → β) {Z : List α} {i : ℕ} (hi : i < Z.length)
    (h : p Z[i] = false) : passList p f Z (i + 1) = passList p f Z i := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, List.map_append]
  simp [h]
theorem length_passList_le (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) :
    (passList p f Z i).length ≤ i := by
  rw [passList, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le i Z)
end Filter
def countTo (L : List ℤ) (i : ℕ) (x : ℤ) : ℤ := ((L.take i).count x : ℤ)
theorem countTo_succ (L : List ℤ) {i : ℕ} (hi : i < L.length) (x : ℤ) :
    countTo L (i + 1) x = countTo L i x + if x = L.getD i 0 then 1 else 0 := by
  rw [countTo, countTo, List.count_take_succ_getD L x hi 0, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one,
    Nat.cast_zero]
  exact congrArg _ (if_congr eq_comm rfl rfl)
theorem countTo_nonneg (L : List ℤ) (i : ℕ) (x : ℤ) : 0 ≤ countTo L i x := Int.natCast_nonneg _
theorem countTo_le (L : List ℤ) (i : ℕ) (x : ℤ) : countTo L i x ≤ i :=
  Int.ofNat_le.2 (List.count_le_length.trans (List.length_take_le i L))
structure DistSt (L D : List ℤ) (i : ℕ) : Prop where
  nodup : D.Nodup
  mem : ∀ x, x ∈ D ↔ x ∈ L.take i
  le : D.length ≤ i
  last : 0 < i → 0 < D.length ∧ D.getD (D.length - 1) 0 = L.getD (i - 1) 0
theorem DistSt.zero (L : List ℤ) : DistSt L [] 0 :=
  ⟨List.nodup_nil, by simp, le_rfl, fun h => absurd h (by omega)⟩
theorem DistSt.opens {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hs : L.Pairwise (· ≤ ·))
    (hi : i < L.length) (hne : D.length = 0 ∨ L.getD i 0 ≠ D.getD (D.length - 1) 0) :
    DistSt L (D ++ [L.getD i 0]) (i + 1) ∧ L.getD i 0 ∉ L.take i := by
  have hnot : L.getD i 0 ∉ L.take i := by
    refine List.getD_notMem_take_of_sorted hs hi 0 ?_
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · obtain ⟨hpos, hlast⟩ := h.last h0
      exact Or.inr (hlast ▸ hne.resolve_left (by omega))
  refine ⟨⟨?_, fun x => ?_, ?_, fun _ => by simp⟩, hnot⟩
  ·
    exact List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, fun a ha b hb e =>
      hnot ((h.mem _).1 (List.mem_singleton.1 hb ▸ e ▸ ha))⟩
  ·
    rw [List.take_succ_getD L hi 0, List.mem_append, List.mem_append, h.mem]
  ·
    rw [List.length_append, List.length_singleton]
    exact Nat.succ_le_succ h.le
theorem DistSt.bumps {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hi : i < L.length)
    (hpos : 0 < D.length) (he : L.getD i 0 = D.getD (D.length - 1) 0) : DistSt L D (i + 1) := by
  refine ⟨h.nodup, fun x => ?_, h.le.trans (Nat.le_succ i), fun _ => ⟨hpos, by simpa using he.symm⟩⟩
  rw [List.take_succ_getD L hi 0, List.mem_append, ← h.mem, List.mem_singleton]
  refine ⟨Or.inl, ?_⟩
  rintro (hx | rfl)
  · exact hx
  · rw [he, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
theorem map_countTo_opens {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hi : i < L.length)
    (hnot : L.getD i 0 ∉ L.take i) :
    (D ++ [L.getD i 0]).map (countTo L (i + 1)) = D.map (countTo L i) ++ [1] := by
  rw [List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left fun x hx => ?_
    rw [countTo_succ L hi, if_neg, add_zero]
    rintro rfl
    exact hnot ((h.mem _).1 hx)
  · rw [countTo_succ L hi, if_pos rfl, countTo, List.count_eq_zero_of_not_mem hnot]
    rfl
theorem map_countTo_bumps {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hi : i < L.length)
    (hpos : 0 < D.length) (he : L.getD i 0 = D.getD (D.length - 1) 0) :
    D.map (countTo L (i + 1)) =
      (D.map (countTo L i)).set (D.length - 1) (countTo L i (D.getD (D.length - 1) 0) + 1) := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  rw [List.length_map] at hj
  have hlast : D.getD (D.length - 1) 0 = D[D.length - 1] := List.getD_eq_getElem _ _ _
  rw [List.getElem_map, countTo_succ L hi, he]
  by_cases hc : j = D.length - 1
  · subst hc
    rw [List.getElem_set_self, if_pos hlast.symm, hlast]
  · rw [List.getElem_set_of_ne (by omega), List.getElem_map, if_neg, add_zero]
    exact fun e => hc ((List.Nodup.getElem_inj_iff h.nodup).1 (e.trans hlast))
end ThreeSumApsp.Spec
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray Finset
variable {lim : Limits} {P : Program}
namespace Resid
end Resid
theorem emodNeed_ok {len V Mo fr d : ℕ} (h : (residNeed len V Mo).Ok lim fr d) :
    (emodNeed V Mo).Ok lim fr (d + 1) := by
  refine h.mono ?_ le_rfl le_rfl
  have hlen : 1 ≤ (len + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc 4 * V + 4 * Mo + 16 ≤ 64 * 1 * (Mo + 1) * (V + 1) := by nlinarith [Nat.zero_le (V * Mo)]
    _ ≤ 64 * (len + 1) ^ 2 * (Mo + 1) * (V + 1) := by gcongr
def ResidInv (μ : ℕ → ℤ) (fr key Mo : ℕ) (sg : ℤ) (L : List ℤ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j (hj : j < L.length), j < i → μ' (key + j) = (sg * L[j]) % (Mo : ℤ)) ∧
    KeptBut μ μ' fr key L.length
theorem ResidInv.succ {μ μ' μ'' : ℕ → ℤ} {fr key Mo i : ℕ} {sg : ℤ} {L : List ℤ}
    (h : ResidInv μ fr key Mo sg L i μ') (hi : i < L.length) (hkey : key + L.length ≤ fr)
    (hkept : Kept μ' μ'' fr) :
    ResidInv μ fr key Mo sg L (i + 1)
      (Function.update μ'' (key + i) ((sg * L[i]) % (Mo : ℤ))) := by
  refine ⟨fun j hj hji => ?_, (h.2.then hkept fun b hb => ⟨hb, hb.1⟩).write (by omega) _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
  · rw [Function.update_of_ne (by omega), hkept _ (by omega), h.1 j hj hji]
  · exact Function.update_self ..
theorem resid_spec {p pEmod : ℕ} (hP : P[p]? = some (residBody pEmod))
    (hEmod : EmodSpec lim P pEmod) : ResidSpec lim P p := by
  intro d fr V Mo s key sg L μ hM hsg hL hseg hs hkey hap hok
  refine ⟨_, hP, ?_⟩
  have hw := hok.space
  have hcells := hok.cells
  have hdepth := hok.depth
  have hword := (emodNeed_ok hok).word
  simp only [residNeed, emodNeed] at hword hdepth
  refine Ends.forShape (fun i (r : ℤ) μ' => ⟨frame [L.length, s, sg, Mo, key, fr, i, r], μ'⟩)
    (ResidInv μ fr key Mo sg L) L.length (tEmod V + 15) 0
    ⟨fun j _ hj => absurd hj (by omega), .refl⟩ ?round ?done
    (first := by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT := by simp [tResid]; ring_nf; omega)
  case round =>
    intro i r μ' hi inv
    have hread : μ' (s + i) = L[i] := by
      rw [inv.2 _ (by omega), hseg i hi]
    have hprod : |sg * L[i]| ≤ (V : ℤ) := by
      rcases hsg with rfl | rfl <;> simpa using hL.getElem hi
    have habs := abs_mul sg L[i]
    refine Ends.callToThen (hEmod (d + 1) fr V Mo (sg * L[i]) μ' hM hprod (emodNeed_ok hok)) ?_
      (by simp [Limits.Addr, abs_le, hread]; omega)
    rintro _ μ'' ⟨rfl, hkept⟩
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (key + i) ((sg * L[i]) % (Mo : ℤ)) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                 )
    exact ⟨_, _, rfl, inv.succ hi hkey hkept⟩
  case done =>
    rintro r μ' ⟨written, kept⟩
    exact ⟨fun j hj => (written j (by simpa using hj) (by simpa using hj)).trans (by simp), kept⟩
namespace Tally
end Tally
def TallyInv (μ : ℕ → ℤ) (cnt cap : ℕ) (δ : ℤ) (K : List ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ r < cap, μ' (cnt + r) = μ (cnt + r) + δ * ((K.take i).count r : ℤ)) ∧ SameOutside μ μ' cnt cap
theorem TallyInv.succ {μ μ' : ℕ → ℤ} {cnt cap i : ℕ} {δ : ℤ} {K : List ℕ}
    (h : TallyInv μ cnt cap δ K i μ') (hi : i < K.length) (hk : K[i] < cap) :
    TallyInv μ cnt cap δ K (i + 1) (Function.update μ' (cnt + K[i]) (μ' (cnt + K[i]) + δ)) := by
  refine ⟨fun r hr => ?_, h.2.write (by omega) _⟩
  rw [List.count_take_succ K r hi]
  by_cases hrk : K[i] = r
  · subst hrk
    rw [Function.update_self, h.1 _ hk, if_pos rfl]
    push_cast
    ring
  · rw [Function.update_of_ne (by omega), h.1 r hr, if_neg hrk, Nat.add_zero]
theorem tally_spec {p : ℕ} (hP : P[p]? = some tallyBody) : TallySpec lim P p := by
  intro d key cnt cap δ K μ hK hδ hseg hap hbd hkey hcnt hw hword
  refine ⟨_, hP, ?_⟩
  refine Ends.forFrame (TallyInv μ cnt cap δ K) K.length ⟨fun r _ => by simp, .refl⟩
    ?round ?done (hT := by simp [tTally]; omega)
  case round =>
    intro i μ' hi inv
    have hk : K[i] < cap := hK _ (List.getElem_mem hi)
    have hread : μ' (key + i) = (K[i] : ℕ) := by
      rw [inv.2 _ (by omega), SegN.getElem hseg hi]
    have hcount : (K.take i).count K[i] ≤ i := List.count_le_length.trans (by simp)
    have hcell := inv.1 _ hk
    have hold := abs_le.1 (hbd _ hk)
    refine Ends.storeTo (cnt + K[i]) (μ' (cnt + K[i]) + δ) ⟨rfl, inv.succ hi hk⟩ ?_
    rcases hδ with rfl | rfl <;> simp [Limits.Addr, abs_le, hread] <;> omega
  case done =>
    exact fun μ' inv => ⟨fun r hr => (inv.1 r hr).trans (by rw [List.take_length]), inv.2⟩
theorem coll_eq_list {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (coll L.toFinset Mo : ℤ)
      = ((keys Mo L).map fun q => ((keys Mo L).count q : ℤ) - 1).sum := by
  rw [coll_eq_sum, List.sum_toFinset _ hL]
  have h : ∀ x ∈ L, ((#(bucket L.toFinset Mo (x % (Mo : ℤ))) - 1 : ℕ) : ℤ)
      = ((keys Mo L).count (x % (Mo : ℤ)).toNat : ℤ) - 1 := by
    intro x hx
    rw [← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    have : 1 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat :=
      List.count_pos_iff.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [Int.natCast_toNat_emod hM x]
    omega
  rw [Nat.cast_list_sum, List.map_map]
  conv_rhs => rw [keys, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun x hx => h x hx)
theorem mem_heavy_iff {S : Finset ℤ} {Mo : ℕ} {x : ℤ} (hx : x ∈ S) :
    x ∈ heavy S Mo ↔ 2 ≤ #(bucket S Mo (x % (Mo : ℤ))) := by
  have hxb : x ∈ bucket S Mo (x % (Mo : ℤ)) := by simp [bucket, hx]
  constructor
  · intro h
    obtain ⟨-, y, hy, hne, hdvd⟩ := Finset.mem_filter.1 h
    have hyb : y ∈ bucket S Mo (x % (Mo : ℤ)) := by
      simp only [bucket, Finset.mem_filter]
      exact ⟨hy, ((natCast_dvd_sub_iff_emod_eq Mo x y).1 hdvd).symm⟩
    exact Finset.one_lt_card.2 ⟨y, hyb, x, hxb, hne⟩
  · intro h
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne h x
    obtain ⟨hyS, hyr⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨hx, y, hyS, hne, (natCast_dvd_sub_iff_emod_eq Mo x y).2 hyr.symm⟩
def heavyList (Mo : ℕ) (L : List ℤ) : List ℤ :=
  L.filter fun x => decide (2 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat)
theorem heavyList_toFinset {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (heavyList Mo L).toFinset = heavy L.toFinset Mo := by
  ext x
  simp only [heavyList, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, h⟩
    rw [mem_heavy_iff (List.mem_toFinset.2 hx), ← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    exact h
  · intro h
    have hx : x ∈ L := List.mem_toFinset.1 (heavy_subset _ _ h)
    refine ⟨hx, ?_⟩
    rw [mem_heavy_iff (List.mem_toFinset.2 hx), ← Int.natCast_toNat_emod hM x,
      card_bucket hM hL] at h
    exact h
structure Counted (μ : ℕ → ℤ) (fr cnt cap : ℕ) (K : List ℕ) : Prop where
  keys : SegN μ fr K
  counts : ∀ q < cap, μ (cnt + q) = (K.count q : ℤ)
theorem sq_add_le_word {n V Mo : ℕ} (h : ((wordNeed n V Mo : ℕ) : ℤ) ≤ lim.word) :
    (n : ℤ) * n + 4 * n + 17 ≤ lim.word := by
  have hMV : 1 ≤ (Mo + 1) * (V + 1) := Nat.mul_pos (by omega) (by omega)
  have hle : n * n + 4 * n + 17 ≤ wordNeed n V Mo :=
    calc n * n + 4 * n + 17 ≤ 64 * (n + 1) ^ 2 * 1 := by nlinarith
      _ ≤ 64 * (n + 1) ^ 2 * ((Mo + 1) * (V + 1)) := Nat.mul_le_mul_left _ hMV
      _ = wordNeed n V Mo := by unfold wordNeed; ring
  exact le_trans (by exact_mod_cast hle) h
theorem sameOn_of_zeroAt {R : ℕ → Prop} {μ μ' : ℕ → ℤ} {cnt cap : ℕ}
    (h : SameOn (fun b => R b ∧ Outside cnt cap b) μ μ') (hz : ZeroAt μ cnt cap)
    (hz' : ZeroAt μ' cnt cap) : SameOn R μ μ' := fun b hb => by
  by_cases hin : Outside cnt cap b
  · exact h b ⟨hb, hin⟩
  · obtain ⟨q, rfl⟩ : ∃ q, b = cnt + q := ⟨b - cnt, by omega⟩
    rw [hz q (by omega), hz' q (by omega)]
theorem Counted.of_sameOutside {μ μ' : ℕ → ℤ} {fr cnt cap a n : ℕ} {K : List ℕ}
    (h : Counted μ fr cnt cap K) (hs : SameOutside μ μ' a n) (hfr : a + n ≤ fr)
    (hap : Apart a n cnt cap) :
    Counted μ' fr cnt cap K :=
  ⟨h.keys.of_sameOutside hs (Or.inr hfr),
    fun q hq => (hs _ (by omega)).trans (h.counts q hq)⟩
theorem BucketMem.exists_pre {μ : ℕ → ℤ} {d fr V Mo s len cnt cap : ℕ} {S : Finset ℤ}
    (h : BucketMem μ fr V Mo s len cnt cap S) (hok : (collNeed len V Mo).Ok lim fr d) :
    ∃ L : List ℤ, L.length = len ∧ L.Nodup ∧ L.toFinset = S ∧
      BucketPre lim μ d fr V Mo s cnt cap L := by
  obtain ⟨L, rfl, hseg, hnd, rfl⟩ := h.set
  exact ⟨L, rfl, hnd, rfl, h.modulus_pos, h.modulus_le,
    fun x hx => h.bdd x (List.mem_toFinset.2 hx), hseg, h.zero, h.belowSet, h.belowTable, h.apart,
    hok⟩
namespace BucketPre
variable {μ μ₁ : ℕ → ℤ} {d fr V Mo s cnt cap pResid pTally : ℕ} {L : List ℤ} {K : List ℕ}
theorem resid_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hResid : ResidSpec lim P pResid)
    {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) :
    Meets lim P pResid (d + 1) [L.length, s, sg, Mo, fr, (fr + L.length : ℕ)] μ (tResid L.length V)
      fun _ μ₁ => SegN μ₁ fr (keys Mo (L.map (sg * ·))) ∧ Kept μ μ₁ fr := by
  have hlist := C.belowList
  refine (hResid (d + 1) (fr + L.length) V Mo s fr sg L μ C.modulus_pos hsg C.bounded C.list
    (by omega) le_rfl (Or.inl hlist) (C.ok.mono le_rfl ?_ ?_)).mono le_rfl ?_
  · simp only [residNeed, collNeed]
    omega
  · simp only [residNeed, collNeed]
    omega
  · rintro _ μ₁ ⟨written, kept⟩
    refine ⟨?_, kept.mono fun b hb => ⟨by omega, Or.inl hb⟩⟩
    rwa [SegN, map_cast_keys C.modulus_pos, List.map_map]
theorem keys_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hResid : ResidSpec lim P pResid) :
    Meets lim P pResid (d + 1) [L.length, s, 1, Mo, fr, (fr + L.length : ℕ)] μ (tResid L.length V)
      fun _ μ₁ => SegN μ₁ fr (keys Mo L) ∧ Kept μ μ₁ fr := by
  simpa using C.resid_meets hResid (Or.inl rfl)
theorem tally_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (hkeys : SegN μ₁ fr K) (hbd : ∀ q < cap, |μ₁ (cnt + q)| ≤ (L.length : ℤ)) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, δ] μ₁ (tTally L.length) fun _ μ₂ =>
      (∀ q < cap, μ₂ (cnt + q) = μ₁ (cnt + q) + δ * (K.count q : ℤ)) ∧
        SameOutside μ₁ μ₂ cnt cap := by
  have hcells := C.ok.cells
  have htable := C.belowTable
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells
  have h := hTally (d + 1) fr cnt cap δ K μ₁ (fun q hq => (hlt q hq).trans_le C.modulus_le) hδ hkeys
    (Or.inr htable)
  rw [hlen] at h
  exact h hbd (by omega) (by omega) C.ok.space (by omega)
theorem count_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (hkeys : SegN μ₁ fr K)
    (kept : Kept μ μ₁ fr) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, 1] μ₁ (tTally L.length) fun _ μ₂ =>
      Counted μ₂ fr cnt cap K ∧ KeptBut μ μ₂ fr cnt cap := by
  have htable := C.belowTable
  have hzero : ZeroAt μ₁ cnt cap := fun q hq => (kept _ (by omega)).trans (C.zero q hq)
  refine (C.tally_meets hTally hlen hlt (Or.inl rfl) hkeys fun q hq => by simp [hzero q hq]).mono
    le_rfl ?_
  rintro _ μ₂ ⟨counts, same⟩
  exact ⟨⟨hkeys.of_sameOutside same (Or.inr htable),
    fun q hq => by rw [counts q hq, hzero q hq]; ring⟩, kept.then same fun b hb => hb⟩
theorem uncount_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (h : Counted μ₁ fr cnt cap K) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, -1] μ₁ (tTally L.length) fun _ μ₂ =>
      ZeroAt μ₂ cnt cap ∧ SameOutside μ₁ μ₂ cnt cap := by
  refine (C.tally_meets hTally hlen hlt (Or.inr rfl) h.keys fun q hq => ?_).mono le_rfl ?_
  · rw [h.counts q hq, abs_of_nonneg (by positivity), ← hlen]
    exact_mod_cast List.count_le_length
  · rintro _ μ₂ ⟨counts, same⟩
    exact ⟨fun q hq => by rw [counts q hq, h.counts q hq]; ring, same⟩
end BucketPre
namespace Coll
end Coll
def collPart (K : List ℕ) (i : ℕ) : ℤ := ((K.take i).map fun q => (K.count q : ℤ) - 1).sum
theorem collPart_succ (K : List ℕ) {i : ℕ} (hi : i < K.length) :
    collPart K (i + 1) = collPart K i + ((K.count K[i] : ℤ) - 1) := by
  unfold collPart
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append, List.sum_append]
  simp
theorem collPart_bounds (K : List ℕ) :
    ∀ i, i ≤ K.length → 0 ≤ collPart K i ∧ collPart K i ≤ (i : ℤ) * (K.length : ℤ) := by
  intro i
  induction i with
  | zero => intro _; simp [collPart]
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh⟩ := ih (by omega)
    have hone : 1 ≤ K.count K[i] := List.count_pos_iff.2 (List.getElem_mem _)
    have hlen : K.count K[i] ≤ K.length := List.count_le_length
    rw [collPart_succ K (by omega)]
    push_cast
    exact ⟨by omega, by nlinarith⟩
theorem collSum_ends {d V s Mo cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L)) :
    Ends lim P d collSum ⟨frame [L.length, s, Mo, cnt, fr, r], μ⟩ (20 * L.length + 10) fun σ' =>
      σ' = ⟨frame [L.length, s, Mo, cnt, fr, r, L.length, collPart (keys Mo L) L.length], μ⟩ := by
  have hw := C.ok.space
  have hword := sq_add_le_word C.ok.word
  have hcells := C.ok.cells
  have htable := C.belowTable
  simp only [collNeed] at hcells
  have hn := length_keys Mo L
  have hK : ∀ q ∈ keys Mo L, q < cap := fun q hq =>
    (keys_lt C.modulus_pos _ q hq).trans_le C.modulus_le
  clear C
  generalize keys Mo L = K at *
  generalize L.length = n at *
  have hsq : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             0
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.for (fun i σ => σ = ⟨frame [n, s, Mo, cnt, fr, r, i, collPart K i], μ⟩) n 12
    ?start ?round ?done ?bound
  case start => simp [update_frame_setLocal, collPart]
  case done => exact fun _ _ hσ => hσ
  case bound =>
    rintro i _ - - rfl
    simp
  case round =>
    rintro i _ hi - rfl
    have hiK : i < K.length := by omega
    have hq : K[i] < cap := hK _ (List.getElem_mem hiK)
    have hkey : μ (fr + i) = (K[i] : ℕ) := counted.keys.getElem hiK
    have hcount := counted.counts _ hq
    have hone : 1 ≤ K.count K[i] := List.count_pos_iff.2 (List.getElem_mem _)
    have hlen : K.count K[i] ≤ n := hn ▸ List.count_le_length
    obtain ⟨hlow, hhigh⟩ := collPart_bounds K i hiK.le
    have hhigh' : collPart K i ≤ (n : ℤ) * n :=
      hhigh.trans (hn ▸ mul_le_mul_of_nonneg_right (by exact_mod_cast hiK.le) (by positivity))
    refine Ends.setTo (collPart K (i + 1)) ⟨by simp, by rw [update_frame_setLocal]; rfl⟩ ?_
    rw [collPart_succ K hiK]
    simp [Limits.Addr, abs_le, hkey, hcount]
    omega
theorem coll_spec {p pResid pTally : ℕ} (hP : P[p]? = some (collBody pResid pTally))
    (hResid : ResidSpec lim P pResid) (hTally : TallySpec lim P pTally) : CollSpec lim P p := by
  intro d fr V Mo s len cnt cap S μ hmem hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hM := C.modulus_pos
  have hw := hok.space
  have hword := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       | refine _root_.Light.Ends.callToThen ((C.keys_meets hResid) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.Light.Ends.callToThen (C.keys_meets hResid) ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tColl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tColl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tColl] <;> omega))
       on_goal -1 =>
         (rintro _ μ₁
             ⟨hkeys, kept₁⟩
                 ;
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                                      )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       |
         refine
           _root_.Light.Ends.callToThen
             ((C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁) _ (by omega)) ?_ ?_
             ?_ ?_
       |
         refine
           _root_.Light.Ends.callToThen
             (C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁) ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tColl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tColl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tColl] <;> omega))
       on_goal -1 =>
         (rintro r μ₂
             ⟨counted, kept₂⟩
                 ;
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                         )
  ((focus
       (repeat
           with_unfolding_none
             first
             | refine _root_.Light.Ends.seqAssoc ?_
             | refine _root_.Light.Ends.skipThen ?_)
       first
       | refine _root_.Light.Ends.pieceThen (collSum_ends C counted) ?_ ?_
       | refine _root_.Light.Ends.pieceLast (collSum_ends C counted) ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tColl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tColl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => rintro _ rfl)
                                                            )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       |
         refine
           _root_.Light.Ends.callToThen
             ((C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L) counted) _ (by omega)) ?_ ?_ ?_
             ?_
       |
         refine
           _root_.Light.Ends.callToThen
             (C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L) counted) ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tColl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tColl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tColl] <;> omega))
       on_goal -1 =>
         (rintro _ μ₃
             ⟨zero₃, same₃⟩
                 ;
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                       )
  refine Ends.setTo (coll L.toFinset Mo : ℤ)
    ⟨by simp, sameOn_of_zeroAt (kept₂.then same₃ fun b hb => ⟨hb, hb.2⟩) C.zero zero₃⟩ ?_
    (by simp [tColl]; omega)
  rw [coll_eq_list hnd hM, collPart, ← length_keys Mo L, List.take_length]
  simp
namespace Heavy
end Heavy
def isHeavy (Mo : ℕ) (L : List ℤ) (x : ℤ) : Bool :=
  decide (2 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat)
abbrev heavyPart (Mo : ℕ) (L : List ℤ) (i : ℕ) : List ℤ := Spec.passList (isHeavy Mo L) id L i
theorem heavyPart_length (Mo : ℕ) (L : List ℤ) : heavyPart Mo L L.length = heavyList Mo L := by
  rw [heavyPart, Spec.passList_length, List.map_id]
  rfl
def HeavyInv (μ : ℕ → ℤ) (s Mo out cnt fr : ℕ) (r : ℤ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [L.length, s, Mo, out, cnt, fr, r, i, (heavyPart Mo L i).length], μ'⟩ ∧
      Seg μ' out (heavyPart Mo L i) ∧ SameOutside μ μ' out L.length
theorem heavyRound_ends {d V s Mo out cnt cap fr i : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) (hi : i < L.length) {σ : State}
    (hσ : HeavyInv μ s Mo out cnt fr r L i σ) :
    Ends lim P d heavyRound σ 22 fun σ' => σ'.loc Heavy.Idx = i ∧
      HeavyInv μ s Mo out cnt fr r L (i + 1)
        { σ' with loc := Function.update σ'.loc Heavy.Idx ((i : ℤ) + 1) } := by
  obtain ⟨μ', rfl, written, same⟩ := hσ
  have hcells := C.ok.cells
  (((obtain ⟨⟩ := _root_.id C; obtain ⟨⟩ := _root_.id O; obtain ⟨⟩ := _root_.id C.ok))
                     )
  simp only [collNeed] at hcells
  have hiK : i < (keys Mo L).length := by rwa [length_keys]
  have hq : (keys Mo L)[i] < Mo := keys_lt C.modulus_pos _ _ (List.getElem_mem hiK)
  have hqi : (keys Mo L)[i] = (L[i] % (Mo : ℤ)).toNat := by simp [keys]
  have hkey : μ' (fr + i) = ((keys Mo L)[i] : ℕ) :=
    (same _ (Or.inr (by omega))).trans (counted.keys.getElem hiK)
  have hcount : μ' (cnt + (keys Mo L)[i]) = ((keys Mo L).count (keys Mo L)[i] : ℤ) :=
    (same _ (by omega)).trans (counted.counts _ (by omega))
  have hread : μ' (s + i) = L[i] := (same _ (by omega)).trans (hL i hi)
  have hj : (heavyPart Mo L i).length ≤ i := Spec.length_passList_le _ _ _ _
  refine Ends.iteLast (fun hheavy => ?_) (fun hlight => ?_)
    (by (((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkey] <;> omega))
                        ))
  · have htwo : 2 ≤ (keys Mo L).count (keys Mo L)[i] :=
      Nat.succ_le_of_lt (by simpa [hkey, hcount] using hheavy)
    have hsucc : heavyPart Mo L (i + 1) = heavyPart Mo L i ++ [L[i]] :=
      Spec.passList_succ_of id hi (by simpa [isHeavy, ← hqi] using htwo)
    ((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (out + (heavyPart Mo L i).length) L[i] ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                   _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                   hread]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hread] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                                                 )
    ((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen ((heavyPart Mo L (i + 1)).length : ℤ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                   _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                   hsucc]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hsucc] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsucc] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                                              )
    exact ⟨by simp, Function.update μ' (out + (heavyPart Mo L i).length) L[i],
        by rw [update_frame_setLocal]; rfl, hsucc ▸ written.snoc _,
        same.update ⟨by omega, by omega⟩ _⟩
  · have hnottwo : ¬ 2 ≤ (keys Mo L).count (keys Mo L)[i] := fun htwo =>
      hlight (by simpa [hkey, hcount] using Nat.lt_of_succ_le htwo)
    have hsucc : heavyPart Mo L (i + 1) = heavyPart Mo L i :=
      Spec.passList_succ_of_not id hi (by simpa [isHeavy, ← hqi] using hnottwo)
    exact Ends.skip
      ⟨by simp, μ', by rw [update_frame_setLocal, hsucc]; rfl, hsucc ▸ written, same⟩
theorem heavyCopy_ends {d V s Mo out cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) :
    Ends lim P d heavyCopy ⟨frame [L.length, s, Mo, out, cnt, fr, r], μ⟩ (30 * L.length + 10)
      (HeavyInv μ s Mo out cnt fr r L L.length) := by
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             0
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.for (HeavyInv μ s Mo out cnt fr r L) L.length 22 ?start ?round ?done ?bound
  case start => exact ⟨μ, by simp [update_frame_setLocal], by simp, .refl⟩
  case round => exact fun i σ hi _ hσ => heavyRound_ends C counted hL O hi hσ
  case done => exact fun _ _ hσ => hσ
  case bound =>
    rintro i _ - - ⟨μ', rfl, -⟩
    simp
theorem heavy_spec {p pResid pTally : ℕ} (hP : P[p]? = some (heavyBody pResid pTally))
    (hResid : ResidSpec lim P pResid) (hTally : TallySpec lim P pTally) : HeavySpec lim P p := by
  intro d fr V Mo s len out cnt cap S μ hmem O hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hout := O.below
  have hapc := O.apartTable
  have hM := C.modulus_pos
  (((obtain ⟨⟩ := _root_.id C; obtain ⟨⟩ := _root_.id hok))
                  )
  have hword := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       | refine _root_.Light.Ends.callToThen ((C.keys_meets hResid) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.Light.Ends.callToThen (C.keys_meets hResid) ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tHeavy]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tHeavy] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tHeavy] <;> omega))
       on_goal -1 =>
         (rintro _ μ₁
             ⟨hkeys, kept₁⟩
                 ;
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                                       )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       |
         refine
           _root_.Light.Ends.callToThen
             ((C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁) _ (by omega)) ?_ ?_
             ?_ ?_
       |
         refine
           _root_.Light.Ends.callToThen
             (C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁) ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tHeavy]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tHeavy] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tHeavy] <;> omega))
       on_goal -1 =>
         (rintro r μ₂ ⟨counted, kept₂⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                          )
  have hseg₂ : Seg μ₂ s L := C.list.keep
  ((focus
       (repeat
           with_unfolding_none
             first
             | refine _root_.Light.Ends.seqAssoc ?_
             | refine _root_.Light.Ends.skipThen ?_)
       first
       | refine _root_.Light.Ends.pieceThen (heavyCopy_ends C counted hseg₂ O) ?_ ?_
       | refine _root_.Light.Ends.pieceLast (heavyCopy_ends C counted hseg₂ O) ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tHeavy]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tHeavy] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => rintro _ ⟨μ₃, rfl, written, same₃⟩)
                                                                                             )
  rw [heavyPart_length] at written
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       |
         refine
           _root_.Light.Ends.callToThen
             ((C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L)
                 (counted.of_sameOutside same₃ hout hapc))
               _ (by omega))
             ?_ ?_ ?_ ?_
       |
         refine
           _root_.Light.Ends.callToThen
             (C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L)
               (counted.of_sameOutside same₃ hout hapc))
             ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 tHeavy]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [tHeavy] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, tHeavy] <;> omega))
       on_goal -1 =>
         (rintro _ μ₄ ⟨zero₄, same₄⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                                                  )
  have hnd' : (heavyList Mo L).Nodup := hnd.filter _
  have hcard : #(heavy L.toFinset Mo) = (heavyList Mo L).length := by
    rw [← heavyList_toFinset hnd hM, List.toFinset_card_of_nodup hnd']
  have hle : (heavyList Mo L).length ≤ L.length := List.length_filter_le _ _
  refine Ends.setTo (#(heavy L.toFinset Mo) : ℤ) ⟨by simp,
    ⟨heavyList Mo L, hcard.symm, written.keep,
      hnd', heavyList_toFinset hnd hM⟩, ?_⟩ (by simp [hcard, heavyPart_length])
    (by simp [tHeavy]; omega)
  exact sameOn_of_zeroAt ((kept₂.then same₃ fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
    fun b hb => ⟨hb, hb.2⟩) C.zero zero₄
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
@[simp] abbrev SearchArgs.vals (x : SearchArgs) : List ℤ :=
  (x.mult : ℤ) :: x.sets ++ [(x.b₁ : ℤ), x.b₂, x.b₃, x.np, x.pr, x.cnt, x.fr]
def searchNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 3⟩
def SearchSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (x : SearchArgs) (μ : ℕ → ℤ), NodeMem μ x.toNodeArgs → 1 ≤ x.mult → x.mult ≤ x.m →
    ∀ d, (searchNeed x.n x.V x.m).Ok lim x.fr d →
    Meets lim P p d x.vals μ (tSearch x.np x.X₁.len x.X₂.len x.X₃.len x.V) fun r μ' =>
      r = (pick {q ∈ Nat.primesLE x.m | x.Good q} : ℤ) ∧ Kept μ μ' x.fr
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ZeroThree
end ZeroThree
namespace Twice
end Twice
structure DistinctMem (μ μ' : ℕ → ℤ) (val mul : ℕ) (L D : List ℤ) (i : ℕ) : Prop where
  values : DistSt L D i
  segVal : Seg μ' val D
  segMul : Seg μ' mul (D.map (countTo L i))
  same : SameOutside2 μ μ' val L.length mul L.length
namespace DistinctMem
variable {μ μ' : ℕ → ℤ} {val mul i : ℕ} {L D : List ℤ}
theorem opens (h : DistinctMem μ μ' val mul L D i) (hs : L.Pairwise (· ≤ ·)) (hi : i < L.length)
    (hap : Apart val L.length mul L.length)
    (hne : D.length = 0 ∨ L.getD i 0 ≠ D.getD (D.length - 1) 0) :
    DistinctMem μ
      (Function.update (Function.update μ' (val + D.length) (L.getD i 0)) (mul + D.length) 1)
      val mul L (D ++ [L.getD i 0]) (i + 1) := by
  obtain ⟨hvalues, hnew⟩ := h.values.opens hs hi hne
  have hle := h.values.le
  refine ⟨hvalues, (h.segVal.snoc _).update_out (by simp; omega) _, ?_,
    (h.same.write (by omega) _).write (by omega) _⟩
  rw [map_countTo_opens h.values hi hnew]
  simpa using (h.segMul.update_out (b := val + D.length) (by simp; omega) (L.getD i 0)).snoc 1
theorem bumps (h : DistinctMem μ μ' val mul L D i) (hi : i < L.length)
    (hap : Apart val L.length mul L.length) (hpos : 0 < D.length)
    (he : L.getD i 0 = D.getD (D.length - 1) 0) :
    DistinctMem μ
      (Function.update μ' (mul + (D.length - 1)) (countTo L i (D.getD (D.length - 1) 0) + 1))
      val mul L D (i + 1) := by
  have hle := h.values.le
  refine ⟨h.values.bumps hi hpos he, h.segVal.update_out (by omega) _, ?_,
    h.same.write (by omega) _⟩
  rw [map_countTo_bumps h.values hi hpos he]
  exact h.segMul.update_in (by simp; omega) _
end DistinctMem
namespace Distinct
end Distinct
def DistinctInv (μ : ℕ → ℤ) (a val mul : ℕ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (D : List ℤ), σ = ⟨frame [L.length, a, val, mul, i, D.length], μ'⟩ ∧
    DistinctMem μ μ' val mul L D i
theorem distinctRound_runs {μ : ℕ → ℤ} {a val mul i : ℕ} {L : List ℤ}
    (C : Distinct.Ctx lim μ a val mul L) (hi : i < L.length) {σ : State}
    (hI : DistinctInv μ a val mul L i σ) :
    distinctRound.Runs lim σ (DistinctInv μ a val mul L (i + 1)) := by
  obtain ⟨μ', D, rfl, hmem⟩ := hI
  have hle := hmem.values.le
  (((obtain ⟨⟩ := _root_.id C))
              )
  have hread : μ' (a + i) = L.getD i 0 :=
    (hmem.same _ ⟨by omega, by omega⟩).trans (C.seg.getD hi 0)
  have hopen := hmem.opens C.sorted hi C.apart
  rw [← hread] at hopen
  by_cases h0 : D.length = 0
  ·
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, distinctRound, distinctOpen,
                       h0] <;>
                     omega))
                                                         ), _, _,
      by simp [distinctRound, distinctOpen, update_frame_setLocal, h0], hopen (.inl h0)⟩
  have haddrVal : ((val : ℤ) + D.length - 1).toNat = val + (D.length - 1) := by omega
  have haddrMul : ((mul : ℤ) + D.length - 1).toNat = mul + (D.length - 1) := by omega
  have hlast : μ' (val + (D.length - 1)) = D.getD (D.length - 1) 0 := hmem.segVal.getD (by omega) 0
  by_cases he : μ' (a + i) = μ' (val + (D.length - 1))
  ·
    have hcount : μ' (mul + (D.length - 1)) = countTo L i (D.getD (D.length - 1) 0) := by
      rw [hmem.segMul (D.length - 1) (by simp; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]
    have := countTo_nonneg L i (D.getD (D.length - 1) 0)
    have := countTo_le L i (D.getD (D.length - 1) 0)
    have hbump := hmem.bumps hi C.apart (by omega) (by rw [← hread, he, hlast])
    rw [← hcount] at hbump
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, distinctRound, h0, he, haddrVal,
                       haddrMul] <;>
                     omega))
                                                                   ), _, _,
      by simp [distinctRound, update_frame_setLocal, h0, he, haddrVal, haddrMul], hbump⟩
  ·
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, distinctRound, distinctOpen, h0,
                       he, haddrVal] <;>
                     omega))
                                                                       ),
      _, _, by simp [distinctRound, distinctOpen, update_frame_setLocal, h0, he, haddrVal],
      hopen (.inr (by rwa [← hlast]))⟩
theorem distinct_spec {p : ℕ} (hP : P[p]? = some distinctBody) : DistinctSpec lim P p := by
  intro d a val mul L μ C
  (((obtain ⟨⟩ := _root_.id C))
              )
  refine Meets.of_body hP ?_
  unfold tDistinct distinctBody
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  refine Ends.next _ (Ends.whileBlock (DistinctInv μ a val mul L) L.length ?start ?round ?done
    (hT := le_rfl)) (by simp [distinctRound, distinctOpen]; omega)
  case start => exact ⟨μ, [], rfl, DistSt.zero L, Seg.nil, Seg.nil, .refl⟩
  case round =>
    intro i σ hi hI
    obtain ⟨μ', D, rfl, -⟩ := id hI
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), distinctRound_runs C hi hI⟩
  case done =>
    rintro _ ⟨μ', D, rfl, hmem⟩
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), Ends.setTo (D.length : ℕ)
      ⟨⟨D, rfl, hmem.values.nodup, ?_, hmem.segVal, ?_⟩, hmem.same⟩
      (hT := by simp [distinctRound, distinctOpen]; omega)⟩
    · ext x
      rw [List.mem_toFinset, List.mem_toFinset, hmem.values.mem, List.take_length]
    · have hcount : countTo L L.length = fun x => (L.count x : ℤ) := by
        funext x
        rw [countTo, List.take_length]
      exact hcount ▸ hmem.segMul
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
namespace Map
variable (a : Map)
theorem layout : a.cx = a.b ∧ a.pr = a.cx + 6 ∧ a.cnt = a.pr + a.m ∧ a.srt = a.cnt + a.m * a.m ∧
    a.val = a.srt + a.n ∧ a.mul = a.val + a.n ∧ a.bt = a.mul + a.n ∧ a.A = a.bt + a.n * a.Λ ∧
    a.tw = a.A + 3 * a.n ∧ a.one = a.tw + a.n ∧ a.top = a.one + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end Map
end Light.Sec3.ChanHe
end
end
section
public section
namespace Light.Sec3.ChanHe
variable {lim : Limits} {P : Program} {p : ℕ}
private theorem clog_le_log_succ (x : ℕ) : Nat.clog 2 x ≤ Nat.log 2 x + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) x).le
theorem emodSpec_of (hP : P[p]? = some emodBody) : EmodSpec lim P p := by
  intro d fr V M x μ hM hx hok
  have hword := hok.word
  have hcells := hok.cells
  simp only [emodNeed] at hword hcells
  push_cast at hword
  have hrounds := emodRounds_le (M := M) (show x.natAbs ≤ V by have := abs_le.mp hx; omega)
  refine (emod_meets hP ⟨hM, hok.space, hword, hcells⟩ hx).mono_time ?_
  unfold tEmod emodTime
  omega
theorem log2Spec_of (hP : P[p]? = some log2Body) : Log2Spec lim P p := by
  intro d x μ hword
  refine (log2_meets hP μ (by push_cast; omega)).mono_time ?_
  unfold tLog2 log2Time
  omega
theorem clog2Spec_of (hP : P[p]? = some clog2Body) : Clog2Spec lim P p := by
  intro d x μ hword
  have := clog_le_log_succ x
  refine (clog2_meets hP μ (by push_cast; omega)).mono_time ?_
  unfold tLog2 clog2Time
  omega
theorem primesSpec_of (hP : P[p]? = some sieveBody) : PrimesSpec lim P p := by
  intro d fr m out μ hout hok
  have hword := hok.word
  have hcells := hok.cells
  simp only [primesNeed] at hword hcells
  push_cast at hword
  refine (sieve_meets hP ⟨hok.space, by push_cast; omega, hout, hcells⟩).mono ?_
    fun _ _ ⟨hcount, hseg, hkept⟩ => ⟨hcount, hseg, hkept.mono fun _ ha => ⟨ha.2, Or.inl ha.1⟩⟩
  unfold tPrimes sieveTime
  rw [mul_assoc 15, mul_assoc 60, mul_add m, mul_add m]
  omega
theorem sortSpec_of {pHalf pMerge pCopy : ℕ} (C : MergeSort.Procs P p pHalf pMerge pCopy) :
    SortSpec lim P p := by
  intro d fr a V L μ hseg _ hbelow hok
  have hword := hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [sortNeed] at hword hcells hdepth
  push_cast at hword
  have hclog := clog_le_log_succ L.length
  refine (sort_meets C hok.space (by omega) hseg hbelow hcells d (by omega)).mono ?_ fun _ _ h => h
  have hmul := Nat.mul_le_mul_left L.length hclog
  unfold tSort sortTime
  rw [mul_assoc 80, mul_add L.length] at *
  omega
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
section memory
variable {μ μ' : ℕ → ℤ} {fr V m np pr cnt s len : ℕ} {S : Finset ℤ} {e : Env} {X : Slot}
  {a : NodeArgs}
theorem SetAt.kept (h : SetAt μ s len S) (hb : s + len ≤ fr) (hk : Kept μ μ' fr) :
    SetAt μ' s len S := by
  obtain ⟨L, hL, hs, hn, ht⟩ := h
  exact ⟨L, hL, hs.congr fun i hi => hk _ (by omega), hn, ht⟩
theorem SetAt.card (h : SetAt μ s len S) : #S = len := by
  obtain ⟨L, hL, -, hn, ht⟩ := h
  rw [← ht, List.toFinset_card_of_nodup hn, hL]
theorem Env.Ok.kept (h : e.Ok μ) (hk : Kept μ μ' e.fr) : e.Ok μ' :=
  { h with
    primes := ⟨h.primes.1, h.primes.2.congr fun i hi => hk _ (by
      have hbelow := h.belowPr
      have hnp := h.primes.1
      simp only [List.length_map, Finset.length_sort] at hi
      omega)⟩
    zero := fun r hr => (hk _ (by have := h.belowCnt; omega)).trans (h.zero r hr) }
theorem Slot.Ok.kept (h : X.Ok μ e) (hk : Kept μ μ' e.fr) : X.Ok μ' e :=
  { h with set := h.set.kept h.below hk }
theorem NodeMem.kept (h : NodeMem μ a) (hk : Kept μ μ' a.fr) : NodeMem μ' a :=
  ⟨h.envOk.kept hk, h.set₁.kept hk, h.set₂.kept hk, h.set₃.kept hk⟩
theorem Slot.Ok.bucket (h : X.Ok μ e) (he : e.Ok μ) {M : ℕ} (hM : 1 ≤ M) (hMm : M ≤ e.m * e.m) :
    BucketMem μ e.fr e.V M X.addr X.len e.cnt (e.m * e.m) X.set :=
  ⟨hM, hMm, h.bdd, h.set, he.zero, h.below, he.belowCnt, h.apart⟩
end memory
theorem mul_le_wordNeed {x y z n V M : ℕ} (hx : x ≤ (n + 1) ^ 2) (hy : y ≤ M + 1)
    (hz : z ≤ 64 * (V + 1)) : x * y * z ≤ wordNeed n V M :=
  calc x * y * z ≤ (n + 1) ^ 2 * (M + 1) * (64 * (V + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
    _ = wordNeed n V M := by unfold wordNeed; ring
theorem mul_le_word {lim : Limits} {x y z n V M : ℕ} (h : ((wordNeed n V M : ℕ) : ℤ) ≤ lim.word)
    (hx : x ≤ (n + 1) ^ 2) (hy : y ≤ M + 1) (hz : z ≤ 64 * (V + 1)) :
    (x : ℤ) * y * z ≤ lim.word :=
  le_trans (by exact_mod_cast mul_le_wordNeed hx hy hz) h
theorem le_word_of_le {lim : Limits} {y n V M : ℕ} (h : ((wordNeed n V M : ℕ) : ℤ) ≤ lim.word)
    (hy : y ≤ M + 1) : (y : ℤ) ≤ lim.word := by
  simpa using mul_le_word (x := 1) (z := 1) h (Nat.one_le_pow _ _ (by omega)) hy (by omega)
theorem wordNeed_mono {n n' V M M' : ℕ} (hn : n ≤ n') (hM : M ≤ M') :
    wordNeed n V M ≤ wordNeed n' V M' := by
  unfold wordNeed
  gcongr
end Light.Sec3.ChanHe
end
end
section
public section
namespace Nat
open Finset
theorem card_primesLE_le (m : ℕ) : #(Nat.primesLE m) ≤ m := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  exact (card_filter_le _ _).trans_eq (by simp)
end Nat
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
variable {lim : Limits} {P : Program}
namespace FirstGood
def hit (good : ℕ → Prop) [DecidablePred good] (l : List ℕ) : ℕ :=
  (l.find? fun q => decide (good q)).getD 0
variable {good : ℕ → Prop} [DecidablePred good]
theorem hit_snoc {l : List ℕ} (hl : ∀ x ∈ l, x ≠ 0) (q : ℕ) :
    hit good (l ++ [q]) = if hit good l = 0 then (if good q then q else 0) else hit good l := by
  unfold hit
  rw [List.find?_append]
  cases h : l.find? fun q => decide (good q) with
  | none =>
    by_cases hq : good q <;> simp [hq]
  | some x =>
    have hx : x ≠ 0 := hl x (List.mem_of_find?_eq_some h)
    simp [hx]
theorem hit_take_succ {l : List ℕ} (hl : ∀ x ∈ l, x ≠ 0) {t : ℕ} (ht : t < l.length) :
    hit good (l.take (t + 1)) = if hit good (l.take t) = 0 then (if good l[t] then l[t] else 0)
      else hit good (l.take t) := by
  rw [List.take_succ_eq_append_getElem ht, hit_snoc fun x hx => hl x (List.mem_of_mem_take hx)]
theorem pick_filter (Q : Finset ℕ) (h0 : ∀ q ∈ Q, q ≠ 0) :
    pick {q ∈ Q | good q}
      = if hit good (Q.sort (· ≤ ·)) = 0 then 1 else hit good (Q.sort (· ≤ ·)) := by
  unfold hit
  cases h : (Q.sort (· ≤ ·)).find? (fun q => decide (good q)) with
  | none =>
    have hempty : ({q ∈ Q | good q} : Finset ℕ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq
      simpa using List.find?_eq_none.1 h q ((Finset.mem_sort _).2 hq)
    simp [pick, hempty]
  | some x =>
    obtain ⟨hx, as, bs, hl, has⟩ := List.find?_eq_some_iff_append.1 h
    have hxQ : x ∈ Q := (Finset.mem_sort (· ≤ ·)).1 (by rw [hl]; simp)
    have hgood : good x := by simpa using hx
    have hmem : x ∈ ({q ∈ Q | good q} : Finset ℕ) := by simp [hxQ, hgood]
    have hne : ({q ∈ Q | good q} : Finset ℕ).Nonempty := ⟨x, hmem⟩
    have hsorted := Finset.pairwise_sort Q (· ≤ ·)
    rw [hl, List.pairwise_append] at hsorted
    have hmin : ({q ∈ Q | good q} : Finset ℕ).min' hne = x := by
      apply le_antisymm (Finset.min'_le _ _ hmem)
      apply Finset.le_min'
      intro y hy
      obtain ⟨hyQ, hyg⟩ := Finset.mem_filter.1 hy
      have hyl : y ∈ as ++ x :: bs := by
        rw [← hl]
        exact (Finset.mem_sort _).2 hyQ
      rcases List.mem_append.1 hyl with hbefore | hfrom
      · exact absurd hyg (by simpa using has y hbefore)
      · rcases List.mem_cons.1 hfrom with rfl | hafter
        · exact le_rfl
        · exact (List.pairwise_cons.1 hsorted.2.1).1 y hafter
    simp [pick, hne, hmin, h0 x hxQ]
theorem pick_bounds {m : ℕ} (hm : 1 ≤ m) {T : Finset ℕ} (hT : T ⊆ Nat.primesLE m) :
    1 ≤ pick T ∧ pick T ≤ m := by
  unfold pick
  split_ifs with h
  · have := Nat.mem_primesLE.1 (hT (Finset.min'_mem T h))
    exact ⟨this.2.one_le, this.1⟩
  · exact ⟨le_rfl, hm⟩
end FirstGood
open FirstGood
namespace Search
end Search
theorem check_ends {pColl : ℕ} (hColl : CollSpec lim P pColl)
    {d fr V Mo s len cnt cap np b xl xs xb : ℕ} {S : Finset ℤ} {loc μ : ℕ → ℤ}
    (hB : BucketMem μ fr V Mo s len cnt cap S) (hok : (collNeed len V Mo).Ok lim fr (d + 1))
    (hprod : (len : ℤ) ^ 2 * np ≤ lim.word) (hxb : xb ≠ Search.Pairs := by decide)
    (hloc : loc xl = len ∧ loc xs = s ∧ loc xb = b ∧ loc Search.Modulus = Mo ∧
      loc Search.Count = cnt ∧ loc Search.Free = fr ∧ loc Search.NumPrimes = np := by
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) :
    Ends lim P d (checkStmt pColl xl xs xb) ⟨loc, μ⟩ (15 + tColl len V) fun σ' =>
      ∃ μ', Kept μ μ' fr ∧ σ' = ⟨updateLocals loc [(Search.Pairs, (coll S Mo : ℤ)),
        (Search.Passed, if coll S Mo * np ≤ b then loc Search.Passed else 0)], μ'⟩ := by
  obtain ⟨el, es, eb, emod, ecnt, efr, enp⟩ := hloc
  have hdepth := hok.depth
  have hcoll : (coll S Mo : ℤ) * np ≤ lim.word := by
    have hsq : coll S Mo ≤ len ^ 2 := hB.set.card ▸ coll_le_sq S Mo
    exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsq) (by positivity)) hprod
  have hnonneg : (0 : ℤ) ≤ (coll S Mo : ℤ) * np := by positivity
  simp only [checkStmt, Search.Modulus, Search.Count, Search.Free, Search.Pairs, Search.NumPrimes,
    Search.Passed]
  refine Ends.callThen (hColl (d + 1) fr V Mo s len cnt cap S μ hB hok) ?_
    (by simp [el, es, emod, ecnt, efr])
  rintro _ μ' ⟨rfl, kept⟩
  refine Ends.iteLast (fun hlarge => ?_) (fun hsmall => ?_) (by simp [enp]; omega)
  ·
    have hlarge' : ¬ coll S Mo * np ≤ b := fun h => by
      have hlt : (b : ℤ) < (coll S Mo : ℤ) * np := by simpa [hxb, eb, enp] using hlarge
      have hle : ((coll S Mo * np : ℕ) : ℤ) ≤ b := by exact_mod_cast h
      push_cast at hle
      omega
    exact Ends.setLast ⟨μ', kept, by simp [if_neg hlarge']⟩ (by simp; omega)
  · have hsmall' : coll S Mo * np ≤ b := by
      have hnlt : ¬ (b : ℤ) < (coll S Mo : ℤ) * np := by simpa [hxb, eb, enp] using hsmall
      exact_mod_cast not_lt.1 hnlt
    refine Ends.skip ⟨μ', kept, ?_⟩
    rw [if_pos hsmall', updateLocals, updateLocals, updateLocals,
      show loc Search.Passed = Function.update loc Search.Pairs
        (coll S Mo : ℤ) Search.Passed by simp,
      Function.update_eq_self]
section search
variable {d pColl : ℕ} {x : SearchArgs} {μ : ℕ → ℤ}
theorem Env.Ok.np_le {e : Env} (h : e.Ok μ) : e.np ≤ e.m * e.m + 1 := by
  have hcard := h.primes.1 ▸ Nat.card_primesLE_le e.m
  have hsq := Nat.le_mul_self e.m
  omega
theorem collNeed_ok_of_search {fr n V m l Mo : ℕ} (hok : (searchNeed n V m).Ok lim fr d)
    (hl : l ≤ n) (hMo : Mo ≤ m * m) : (collNeed l V Mo).Ok lim fr (d + 1) :=
  hok.mono (wordNeed_mono hl hMo) (by simp only [collNeed, searchNeed]; omega)
    (by simp only [collNeed, searchNeed]; omega)
def tChecks (x : SearchArgs) : ℕ :=
  45 + (tColl x.X₁.len x.V + tColl x.X₂.len x.V + tColl x.X₃.len x.V)
theorem searchChecks_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ x.toNodeArgs)
    (hok : (searchNeed x.n x.V x.m).Ok lim x.fr d) {q t found : ℕ} {c : ℤ}
    (hM1 : 1 ≤ x.mult * q) (hM : x.mult * q ≤ x.m * x.m) :
    Ends lim P d (searchChecks pColl)
      ⟨frame (x.vals ++ [(t : ℤ), found, (x.mult * q : ℕ), c, 1]), μ⟩ (tChecks x) fun σ' =>
      ∃ (c' : ℤ) (μ' : ℕ → ℤ), Kept μ μ' x.fr ∧ σ' = ⟨frame (x.vals ++
        [(t : ℤ), found, (x.mult * q : ℕ), c', if x.Good q then 1 else 0]), μ'⟩ := by
  have hprod : ∀ l ≤ x.n, (l : ℤ) ^ 2 * x.np ≤ lim.word := fun l hl => by
    simpa using mul_le_word (x := l ^ 2) (z := 1) hok.word (Nat.pow_le_pow_left (by omega) 2)
      hN.envOk.np_le (by omega)
  unfold tChecks
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (check_ends hColl (hN.set₁.bucket hN.envOk hM1 hM)
                 (collNeed_ok_of_search hok hN.set₁.le hM) (hprod _ hN.set₁.le))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (check_ends hColl (hN.set₁.bucket hN.envOk hM1 hM)
                 (collNeed_ok_of_search hok hN.set₁.le hM) (hprod _ hN.set₁.le))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨μ₁, kept₁, rfl⟩))
                                                                                          )
  have hN₁ := hN.kept kept₁
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (check_ends hColl (hN₁.set₂.bucket hN₁.envOk hM1 hM)
                 (collNeed_ok_of_search hok hN.set₂.le hM) (hprod _ hN.set₂.le))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (check_ends hColl (hN₁.set₂.bucket hN₁.envOk hM1 hM)
                 (collNeed_ok_of_search hok hN.set₂.le hM) (hprod _ hN.set₂.le))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨μ₂, kept₂, rfl⟩))
                                                                                          )
  have hN₂ := hN₁.kept kept₂
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (check_ends hColl (hN₂.set₃.bucket hN₂.envOk hM1 hM)
                 (collNeed_ok_of_search hok hN.set₃.le hM) (hprod _ hN.set₃.le))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (check_ends hColl (hN₂.set₃.bucket hN₂.envOk hM1 hM)
                 (collNeed_ok_of_search hok hN.set₃.le hM) (hprod _ hN.set₃.le))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨μ₃, kept₃, rfl⟩))
                                                                                          )
  refine ⟨coll x.X₃.set (x.mult * q), μ₃, kept₁.trans (kept₂.trans kept₃), ?_⟩
  by_cases h₁ : coll x.X₁.set (x.mult * q) * x.np ≤ x.b₁ <;>
    by_cases h₂ : coll x.X₂.set (x.mult * q) * x.np ≤ x.b₂ <;>
    by_cases h₃ : coll x.X₃.set (x.mult * q) * x.np ≤ x.b₃ <;>
    simp [update_frame_setLocal, SearchArgs.Good, h₁, h₂, h₃]
abbrev SearchArgs.candidates (x : SearchArgs) : List ℕ := (Nat.primesLE x.m).sort (· ≤ ·)
def SearchInv (μ : ℕ → ℤ) (x : SearchArgs) (t : ℕ) (σ : State) : Prop :=
  ∃ (y z w : ℤ) (μ' : ℕ → ℤ), Kept μ μ' x.fr ∧
    σ = ⟨frame (x.vals ++ [(t : ℤ), (hit x.Good (x.candidates.take t) : ℕ), y, z, w]), μ'⟩
theorem searchRecord_ends {g : Prop} [Decidable g] {t found q : ℕ} {y c : ℤ}
    (hread : μ (x.pr + t) = (q : ℕ)) (hpr : x.pr + t < lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hone : (1 : ℤ) ≤ lim.word) :
    Ends lim P d searchRecord
      ⟨frame (x.vals ++ [(t : ℤ), found, y, c, if g then 1 else 0]), μ⟩ 13 fun σ' =>
      σ' = ⟨frame (x.vals ++ [(t : ℤ),
        ((if found = 0 then (if g then q else 0) else found : ℕ) : ℤ), y, c,
        if g then 1 else 0]), μ⟩ := by
  by_cases hg : g
  · simp only [if_pos hg]
    refine Ends.iteLast (fun _ => ?_) (fun h => absurd h (by simp))
    refine Ends.iteLast (fun hfirst => ?_) (fun hlater => ?_)
    · have hzero : found = 0 := by simpa using hfirst
      exact Ends.setTo (q : ℤ) (by simp [hzero]) (by (((  (try have := _root_.Light.Std.space_le (by assumption))
                                                          (try have := _root_.Light.Std.const_le (by assumption))
                                                          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))
                                                                      ))
    · have hpos : ¬ found = 0 := by simpa using hlater
      exact Ends.skip (by simp [hpos])
  · simp only [if_neg hg]
    refine Ends.iteLast (fun h => absurd h (by simp)) (fun _ => Ends.skip ?_)
    by_cases hzero : found = 0 <;> simp [hzero]
theorem searchRound_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ x.toNodeArgs)
    (hmult_pos : 1 ≤ x.mult) (hmult_le : x.mult ≤ x.m)
    (hok : (searchNeed x.n x.V x.m).Ok lim x.fr d) {t : ℕ} (ht : t < x.np) {σ : State}
    (hσ : SearchInv μ x t σ) :
    Ends lim P d (searchRound pColl) σ (tChecks x + 22) fun σ' =>
      σ'.loc Search.Idx = t ∧ SearchInv μ x (t + 1)
        { σ' with loc := Function.update σ'.loc Search.Idx ((t : ℤ) + 1) } := by
  obtain ⟨y, z, w, μ', kept, rfl⟩ := hσ
  have hN' := hN.kept kept
  unfold SearchInv
  generalize hps : x.candidates = ps at *
  have htl : t < ps.length := by rw [← hps, Finset.length_sort, ← hN.envOk.primes.1]; exact ht
  have hprime : ∀ q ∈ ps, q.Prime ∧ q ≤ x.m := fun q hq => by
    rw [← hps, Finset.mem_sort, Nat.mem_primesLE] at hq
    exact ⟨hq.2, hq.1⟩
  obtain ⟨hqp, hqm⟩ := hprime ps[t] (List.getElem_mem htl)
  have hread : μ' (x.pr + t) = (ps[t] : ℕ) := SegN.getElem (hps ▸ hN'.envOk.primes.2) htl
  have hsucc := hit_take_succ (good := x.Good) (fun q hq => (hprime q hq).1.ne_zero) htl
  have hMo : x.mult * ps[t] ≤ x.m * x.m := Nat.mul_le_mul hmult_le hqm
  have hMw : (x.mult : ℤ) * ps[t] ≤ lim.word := by
    exact_mod_cast le_word_of_le (y := x.mult * ps[t]) hok.word (by omega)
  have hMpos : (1 : ℤ) ≤ (x.mult : ℤ) * ps[t] := by
    exact_mod_cast Nat.mul_pos hmult_pos hqp.one_le
  have hw := hok.space
  have hcells := hok.cells
  have hpr := hN.envOk.belowPr
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (x.mult * ps[t] : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hread]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hread] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                           )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             1
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (searchChecks_ends hColl hN' hok (Nat.mul_pos hmult_pos hqp.one_le) hMo) ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (searchChecks_ends hColl hN' hok (Nat.mul_pos hmult_pos hqp.one_le) hMo) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨c, μ'', kept', rfl⟩
                 ))
                              )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (searchRecord_ends ((kept' _ (by omega)).trans hread) (by omega) hw (by omega)) ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (searchRecord_ends ((kept' _ (by omega)).trans hread) (by omega) hw (by omega)) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ rfl))
             )
  exact ⟨by simp, _, c, _, μ'', kept.trans kept', by rw [update_frame_setLocal, hsucc]; rfl⟩
theorem search_spec {p : ℕ} (hP : P[p]? = some (searchBody pColl)) (hColl : CollSpec lim P pColl) :
    SearchSpec lim P p := by
  intro x μ hN hmult_pos hmult_le d hok
  refine .of_body hP ?_
  have hone : ((1 : ℕ) : ℤ) ≤ lim.word := le_word_of_le hok.word (by omega)
  have hnp : (x.np : ℤ) ≤ lim.word := le_word_of_le hok.word hN.envOk.np_le
  refine Ends.setToThen 0 ?_ (hT := by simp [tSearch])
  refine Ends.next _ (Ends.for (SearchInv μ x) x.np (tChecks x + 22) ?start ?round ?done ?bound
    (hT := le_rfl)) (by simp [tSearch, tChecks]; ring_nf; omega)
  case start =>
    exact ⟨0, 0, 0, μ, .refl, by rw [update_frame_setLocal, ← frame_append_zeros _ 3]; rfl⟩
  case round => exact fun t σ ht _ hσ => searchRound_ends hColl hN hmult_pos hmult_le hok ht hσ
  case done =>
    rintro _ - ⟨y, z, w, μ', kept, rfl⟩
    have hpick := pick_filter (good := x.Good) (Nat.primesLE x.m)
      fun q hq => (Nat.prime_of_mem_primesLE hq).ne_zero
    rw [List.take_of_length_le (by rw [Finset.length_sort, hN.envOk.primes.1])]
    generalize hit x.Good x.candidates = found at *
    refine Ends.iteLast (fun hnone => ?_) (fun hsome => ?_)
      (hT := by simp [tSearch, tChecks]; ring_nf; omega)
    · have hzero : found = 0 := by simpa using hnone
      exact Ends.setTo 1 ⟨by simp [hpick, hzero], kept⟩
        (hT := by simp [tSearch, tChecks]; ring_nf; omega)
    · have hpos : ¬ found = 0 := by simpa using hsome
      exact Ends.setTo found ⟨by simp [hpick, hpos], kept⟩
        (hT := by simp [tSearch, tChecks]; ring_nf; omega)
  case bound =>
    rintro t _ - - ⟨y, z, w, μ', -, rfl⟩
    simp
end search
namespace Modulus
end Modulus
section modulus
variable {d Λ pSearch pColl : ℕ} {a : NodeArgs} {μ : ℕ → ℤ}
@[simp] def NodeArgs.firstSearch (a : NodeArgs) (Λ : ℕ) : SearchArgs :=
  { toNodeArgs := a, mult := 1, b₁ := 3 * Λ * a.X₁.len * a.X₁.len,
    b₂ := 3 * Λ * a.X₂.len * a.X₂.len, b₃ := 3 * Λ * a.X₃.len * a.X₃.len }
@[simp] def NodeArgs.secondSearch (a : NodeArgs) (Λ p₁ : ℕ) : SearchArgs :=
  { toNodeArgs := a, mult := p₁, b₁ := 3 * Λ * coll a.X₁.set p₁, b₂ := 3 * Λ * coll a.X₂.set p₁,
    b₃ := 3 * Λ * coll a.X₃.set p₁ }
theorem search_meets_firstP (hSearch : SearchSpec lim P pSearch) (hN : NodeMem μ a) (hm : 1 ≤ a.m)
    (hok : (searchNeed a.n a.V a.m).Ok lim a.fr d) :
    Meets lim P pSearch d (a.firstSearch Λ).vals μ (tSearch a.np a.X₁.len a.X₂.len a.X₃.len a.V)
      fun r μ' => r = (firstP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧
        Kept μ μ' a.fr := by
  refine (hSearch (a.firstSearch Λ) μ hN le_rfl hm d hok).mono le_rfl ?_
  rintro _ μ' ⟨rfl, kept⟩
  refine ⟨?_, kept⟩
  unfold firstP SearchArgs.Good
  simp only [NodeArgs.firstSearch, one_mul, ← hN.envOk.primes.1, hN.set₁.set.card, hN.set₂.set.card,
    hN.set₃.set.card, sq, mul_assoc]
theorem search_meets_secondP (hSearch : SearchSpec lim P pSearch) (hN : NodeMem μ a) {p₁ : ℕ}
    (hp₁_pos : 1 ≤ p₁) (hp₁_le : p₁ ≤ a.m) (hok : (searchNeed a.n a.V a.m).Ok lim a.fr d) :
    Meets lim P pSearch d (a.secondSearch Λ p₁).vals μ
      (tSearch a.np a.X₁.len a.X₂.len a.X₃.len a.V)
      fun r μ' => r = (secondP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set p₁ : ℤ) ∧
        Kept μ μ' a.fr := by
  refine (hSearch (a.secondSearch Λ p₁) μ hN hp₁_pos hp₁_le d hok).mono le_rfl ?_
  rintro _ μ' ⟨rfl, kept⟩
  refine ⟨?_, kept⟩
  unfold secondP SearchArgs.Good
  simp only [NodeArgs.secondSearch, ← hN.envOk.primes.1]
  rfl
section words
variable {n V m : ℕ}
theorem three_lam_mul_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {x : ℕ} (hx : x ≤ (n + 1) ^ 2) : 0 ≤ 3 * (Λ : ℤ) * x ∧ 3 * (Λ : ℤ) * x ≤ lim.word := by
  have h := mul_le_word (y := 1) (z := 3 * Λ) hword hx (by omega) (by omega)
  push_cast at h
  exact ⟨by positivity, by linarith⟩
theorem three_lam_sq_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {l : ℕ} (hl : l ≤ n) : (0 ≤ 3 * (Λ : ℤ) * l ∧ 3 * (Λ : ℤ) * l ≤ lim.word) ∧
      0 ≤ 3 * (Λ : ℤ) * l * l ∧ 3 * (Λ : ℤ) * l * l ≤ lim.word := by
  have hsq : l * l ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h := three_lam_mul_le hword hΛ hsq
  push_cast at h
  rw [← mul_assoc] at h
  exact ⟨three_lam_mul_le hword hΛ ((Nat.le_mul_self l).trans hsq), h⟩
theorem three_lam_coll_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {s l M : ℕ} {S : Finset ℤ} (hS : SetAt μ s l S) (hl : l ≤ n) :
    0 ≤ 3 * (Λ : ℤ) * coll S M ∧ 3 * (Λ : ℤ) * coll S M ≤ lim.word :=
  three_lam_mul_le hword hΛ ((coll_le_sq S M).trans (hS.card ▸ Nat.pow_le_pow_left (by omega) 2))
end words
theorem Slot.Ok.coll_meets {e : Env} {X : Slot} {M : ℕ} (h : X.Ok μ e) (he : e.Ok μ)
    (hColl : CollSpec lim P pColl) (hM : 1 ≤ M) (hMm : M ≤ e.m * e.m)
    (hok : (collNeed X.len e.V M).Ok lim e.fr d) :
    Meets lim P pColl d [X.len, X.addr, M, e.cnt, e.fr] μ (tColl X.len e.V) fun r μ' =>
      r = (coll X.set M : ℤ) ∧ Kept μ μ' e.fr :=
  hColl d _ _ _ _ _ _ _ _ μ (h.bucket he hM hMm) hok
theorem modulusColls_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ a)
    (hok : (modulusNeed a.n a.V a.m).Ok lim a.fr d) {p₁ : ℕ} (hp₁_pos : 1 ≤ p₁)
    (hp₁_le_sq : p₁ ≤ a.m * a.m) :
    Ends lim P d (modulusColls pColl) ⟨frame (a.modulusVals Λ ++ [(p₁ : ℤ)]), μ⟩
      (21 + (tColl a.X₁.len a.V + tColl a.X₂.len a.V + tColl a.X₃.len a.V)) fun σ' =>
      ∃ μ', Kept μ μ' a.fr ∧ σ' = ⟨frame (a.modulusVals Λ ++
        [(p₁ : ℤ), 0, coll a.X₁.set p₁, coll a.X₂.set p₁, coll a.X₃.set p₁]), μ'⟩ := by
  have hdepth := hok.depth
  simp only [modulusNeed] at hdepth
  have hokC : ∀ {l : ℕ}, l ≤ a.n → (collNeed l a.V p₁).Ok lim a.fr (d + 1) := fun hl =>
    hok.mono (wordNeed_mono hl hp₁_le_sq) (by simp only [collNeed, modulusNeed]; omega)
      (by simp only [collNeed, modulusNeed]; omega)
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hN.set₁.coll_meets hN.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₁.le)) _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hN.set₁.coll_meets hN.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₁.le)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨rfl, kept₁⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  have hN₁ := hN.kept kept₁
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hN₁.set₂.coll_meets hN₁.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₂.le)) _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hN₁.set₂.coll_meets hN₁.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₂.le)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨rfl, kept₂⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  have hN₂ := hN₁.kept kept₂
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hN₂.set₃.coll_meets hN₂.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₃.le)) _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hN₂.set₃.coll_meets hN₂.envOk hColl hp₁_pos hp₁_le_sq (hokC hN.set₃.le)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₃ ⟨rfl, kept₃⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  exact ⟨μ₃, kept₁.trans (kept₂.trans kept₃), rfl⟩
theorem modulusMain_ends (hSearch : SearchSpec lim P pSearch) (hColl : CollSpec lim P pColl)
    (hN : NodeMem μ a) (hΛ : Λ ≤ a.V + 2) (hok : (modulusNeed a.n a.V a.m).Ok lim a.fr d)
    (hm : 1 ≤ a.m) :
    Ends lim P d (modulusMain pSearch pColl) ⟨frame (a.modulusVals Λ), μ⟩
      (tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V - 73) fun σ' =>
      σ'.loc Modulus.Result = (modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧
        Kept μ σ'.mem a.fr := by
  have hdepth := hok.depth
  simp only [modulusNeed] at hdepth
  have hokS : (searchNeed a.n a.V a.m).Ok lim a.fr (d + 1) :=
    hok.mono le_rfl le_rfl (by simp only [searchNeed, modulusNeed]; omega)
  obtain ⟨p₁, hfirst⟩ : ∃ p₁, p₁ = firstP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set :=
    ⟨_, rfl⟩
  obtain ⟨p₂, hsecond⟩ :
      ∃ p₂, p₂ = secondP (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set p₁ := ⟨_, rfl⟩
  obtain ⟨hp₁_pos, hp₁_le⟩ : 1 ≤ p₁ ∧ p₁ ≤ a.m := by
    rw [hfirst, firstP]
    exact pick_bounds hm (Finset.filter_subset _ _)
  obtain ⟨-, hp₂_le⟩ : 1 ≤ p₂ ∧ p₂ ≤ a.m := by
    rw [hsecond, secondP]
    exact pick_bounds hm (Finset.filter_subset _ _)
  have hthree := three_lam_mul_le (Λ := 1) hok.word (by omega) (x := 1)
    (Nat.one_le_pow _ _ (by omega))
  have hlam := three_lam_mul_le hok.word hΛ (x := 1) (Nat.one_le_pow _ _ (by omega))
  have hlen₁ := three_lam_sq_le hok.word hΛ hN.set₁.le
  have hlen₂ := three_lam_sq_le hok.word hΛ hN.set₂.le
  have hlen₃ := three_lam_sq_le hok.word hΛ hN.set₃.le
  have hcoll₁ := three_lam_coll_le (M := p₁) hok.word hΛ hN.set₁.set hN.set₁.le
  have hcoll₂ := three_lam_coll_le (M := p₁) hok.word hΛ hN.set₂.set hN.set₂.le
  have hcoll₃ := three_lam_coll_le (M := p₁) hok.word hΛ hN.set₃.set hN.set₃.le
  have hprod : 0 ≤ (p₁ : ℤ) * p₂ ∧ (p₁ : ℤ) * p₂ ≤ lim.word := ⟨by positivity, by
    exact_mod_cast le_word_of_le (y := p₁ * p₂) hok.word
      ((Nat.mul_le_mul hp₁_le hp₂_le).trans (by omega))⟩
  simp only [tModulus]
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((search_meets_firstP (Λ := Λ) hSearch hN hm hokS) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (search_meets_firstP (Λ := Λ) hSearch hN hm hokS) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨rfl, kept₁⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                    )
  rw [← hfirst]
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (modulusColls_ends hColl (hN.kept kept₁) hok hp₁_pos
                 (hp₁_le.trans (Nat.le_mul_self a.m)))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (modulusColls_ends hColl (hN.kept kept₁) hok hp₁_pos
                 (hp₁_le.trans (Nat.le_mul_self a.m)))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨μ₂, kept₂, rfl⟩
                 ))
                                                                )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((search_meets_secondP (Λ := Λ) hSearch ((hN.kept kept₁).kept kept₂) hp₁_pos hp₁_le
                   hokS)
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (search_meets_secondP (Λ := Λ) hSearch ((hN.kept kept₁).kept kept₂) hp₁_pos hp₁_le hokS)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₃ ⟨rfl, kept₃⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                              )
  rw [← hsecond]
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen ((p₁ : ℤ) * p₂) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                          )
  refine ⟨?_, kept₁.trans (kept₂.trans kept₃)⟩
  simp [modulus, ← hfirst, ← hsecond]
theorem modulus_spec {p : ℕ} (hP : P[p]? = some (modulusBody pSearch pColl))
    (hSearch : SearchSpec lim P pSearch) (hColl : CollSpec lim P pColl) : ModulusSpec lim P p := by
  intro a Λ μ hN hΛ d hok
  refine .of_body hP ?_
  have hone : ((1 : ℕ) : ℤ) ≤ lim.word := le_word_of_le hok.word (by omega)
  have hcard := hN.envOk.primes.1
  refine Ends.iteLast (fun hnone => ?_) (fun hsome => ?_) (hT := by simp [tModulus])
  ·
    have hempty : Nat.primesLE a.m = ∅ := Finset.card_eq_zero.1 (by
      have hnp : a.np = 0 := by simpa using hnone
      omega)
    exact Ends.setTo 1 ⟨by simp [modulus, firstP, secondP, pick, hempty], .refl⟩
      (hT := by simp [tModulus])
  · have hm : 1 ≤ a.m := by
      have hpos : 0 < #(Nat.primesLE a.m) := by
        have hnp : ¬ a.np = 0 := by simpa using hsome
        omega
      obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
      exact (Nat.prime_of_mem_primesLE hq).one_le.trans (Nat.le_of_mem_primesLE hq)
    exact (modulusMain_ends hSearch hColl hN hΛ hok hm).mono (by simp [tModulus]) fun _ h => h
theorem modulusSpec_of {p : ℕ} (hP : P[p]? = some (modulusBody pSearch pColl))
    (hPs : P[pSearch]? = some (searchBody pColl)) (hColl : CollSpec lim P pColl) :
    ModulusSpec lim P p :=
  modulus_spec hP (search_spec hPs hColl) hColl
end modulus
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ArrLocals
end ArrLocals
def padVal (V : ℕ) (t : ℕ) : ℤ :=
  if t = 0 then 10 * (6 * V + 4) else if t = 1 then (2 * V + 1) + (6 * V + 4)
  else if t = 2 then (2 * V + 1) + 3 * (6 * V + 4) else -(2 * V + 1) + 4 * (6 * V + 4)
structure ArrScratch : Type where
  idx : ℤ
  ad : ℤ
  key : ℤ
  val : ℤ
  res : ℤ
  fr2 : ℤ
abbrev arrLocals (a : ArrArgs) (x : ArrScratch) (sg g : ℤ) (s len off δ : ℕ) : List ℤ :=
  [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr, 2 * a.V + 1, 6 * a.V + 4,
    x.idx, x.ad, x.key, x.val, x.res, (2 * (a.m * a.m) : ℕ), sg, g, s, len, off, δ, x.fr2,
    padVal a.V 0, padVal a.V 1, padVal a.V 2, padVal a.V 3]
def PadInv (μ : ℕ → ℤ) (y c : ℕ) (p : ℕ → ℤ) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < j, ∀ t < 4, μ' (y + 4 * i + t) = p t) ∧ SameOutside μ μ' y (4 * c)
theorem PadInv.succ {μ μ' : ℕ → ℤ} {y c j : ℕ} {p : ℕ → ℤ} (h : PadInv μ y c p j μ') (hj : j < c) :
    PadInv μ y c p (j + 1) (Function.update (Function.update (Function.update (Function.update μ'
      (y + 4 * j) (p 0)) (y + 4 * j + 1) (p 1)) (y + 4 * j + 2) (p 2)) (y + 4 * j + 3) (p 3)) := by
  refine ⟨fun i hi t ht => ?_, (((h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩
    _).update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.1 i hlt t ht]
  · interval_cases t <;> simp
theorem pad_ends {μ : ℕ → ℤ} {a : ArrArgs} (hw : (lim.space : ℤ) ≤ lim.word)
    (hy : a.y + 4 * (2 * (a.m * a.m)) ≤ lim.space) {x : ArrScratch} {sg g : ℤ}
    {s len off δ : ℕ} :
    Ends lim P d padStmt ⟨frame (arrLocals a x sg g s len off δ), μ⟩ (42 * (2 * (a.m * a.m)) + 6)
      fun σ' => ∃ μ', PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V) (2 * (a.m * a.m)) μ' ∧
        σ' = ⟨frame (arrLocals a { x with idx := (2 * (a.m * a.m) : ℕ) } sg g s len off δ),
          μ'⟩ := by
  refine Ends.forFrame (PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V)) (2 * (a.m * a.m))
    ⟨fun i hi => absurd hi (by omega), .refl⟩ ?round ?done
  case round =>
    intro j μ' hj inv
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (a.y + 4 * j) (padVal a.V 0) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                           )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (a.y + 4 * j + 1) (padVal a.V 1) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                               )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (a.y + 4 * j + 2) (padVal a.V 2) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                               )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (a.y + 4 * j + 3) (padVal a.V 3) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                               )
    exact ⟨rfl, inv.succ hj⟩
  case done => exact fun μ' inv => ⟨μ', inv, rfl⟩
def tPlace (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 45 * len + 32
def PlaceCell (y off δ Mo b : ℕ) : Prop := ∃ r < Mo, b = y + 4 * r + off ∨ b = y + 4 * r + off + δ
structure PlaceInv (μ μ' : ℕ → ℤ) (y off δ Mo : ℕ) (K : List ℕ) (val : ℕ → ℤ) (j : ℕ) : Prop where
  cells : ∀ r < Mo, ∀ e, (e = 0 ∨ e = δ) → μ' (y + 4 * r + off + e) =
    if K.count r = 1 ∧ r ∈ K.take j then val r else μ (y + 4 * r + off + e)
  rest : SameOn (fun b => ¬ PlaceCell y off δ Mo b) μ μ'
namespace PlaceInv
variable {μ μ' : ℕ → ℤ} {y off δ Mo j : ℕ} {K : List ℕ} {val : ℕ → ℤ}
theorem zero : PlaceInv μ μ y off δ Mo K val 0 := ⟨fun r _ e _ => by simp, .refl⟩
theorem mem_take_succ (hj : j < K.length) (r : ℕ) :
    r ∈ K.take (j + 1) ↔ r ∈ K.take j ∨ r = K[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
theorem succ_one (h : PlaceInv μ μ' y off δ Mo K val j) (hj : j < K.length) (hlt : K[j] < Mo)
    (hone : K.count K[j] = 1) (hδ : δ = 0 ∨ 4 * Mo ≤ δ) :
    PlaceInv μ (Function.update (Function.update μ' (y + 4 * K[j] + off) (val K[j]))
      (y + 4 * K[j] + off + δ) (val K[j])) y off δ Mo K val (j + 1) := by
  refine ⟨fun r hr e he => ?_, fun b hb => ?_⟩
  · by_cases hrK : r = K[j]
    · subst hrK
      rw [if_pos ⟨hone, (mem_take_succ hj _).2 (Or.inr rfl)⟩]
      rcases he with rfl | rfl <;> simp [Function.update_apply]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.cells r hr e he]
      simp only [mem_take_succ hj, hrK, or_false]
  · rw [Function.update_of_ne fun hEq => hb ⟨_, hlt, Or.inr hEq⟩,
      Function.update_of_ne fun hEq => hb ⟨_, hlt, Or.inl hEq⟩, h.rest b hb]
theorem succ_many (h : PlaceInv μ μ' y off δ Mo K val j) (hj : j < K.length)
    (hmany : K.count K[j] ≠ 1) : PlaceInv μ μ' y off δ Mo K val (j + 1) := by
  refine ⟨fun r hr e he => ?_, h.rest⟩
  rw [h.cells r hr e he]
  by_cases hrK : r = K[j]
  · subst hrK
    simp [hmany]
  · simp only [mem_take_succ hj, hrK, or_false]
theorem done (h : PlaceInv μ μ' y off δ Mo K val K.length) {r : ℕ} (hr : r < Mo) {e : ℕ}
    (he : e = 0 ∨ e = δ) : μ' (y + 4 * r + off + e) =
      if K.count r = 1 then val r else μ (y + 4 * r + off + e) := by
  rw [h.cells r hr e he, List.take_length]
  by_cases hone : K.count r = 1
  · rw [if_pos ⟨hone, List.count_pos_iff.1 (by omega)⟩, if_pos hone]
  · rw [if_neg fun h => hone h.1, if_neg hone]
end PlaceInv
section pass
variable {μ μ₀ : ℕ → ℤ} {a : ArrArgs} {sg g : ℤ} {s off δ cap ylen : ℕ} {L : List ℤ} {K : List ℕ}
  {val : ℕ → ℤ}
theorem PassPre.placeCell_lt (H : PassPre lim μ₀ d a sg g s off δ cap ylen L) {b : ℕ}
    (hb : PlaceCell a.y off δ a.Mo b) : a.y ≤ b ∧ b < a.y + ylen := by
  obtain ⟨r, hr, hb⟩ := hb
  (((obtain ⟨⟩ := _root_.id H))
              )
  omega
theorem placeRound_ends (H : PassPre lim μ₀ d a sg g s off δ cap ylen L)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < a.Mo) (counted : Counted μ a.fr a.cnt cap K)
    (hL : Seg μ s L) (hval : ∀ j (hK : j < K.length) (hj : j < L.length), K.count K[j] = 1 →
      sg * L[j] + g = val K[j]) (x : ArrScratch) {j : ℕ} (hj : j < L.length) {μ' : ℕ → ℤ}
    (inv : PlaceInv μ μ' a.y off δ a.Mo K val j) :
    Ends lim P d placeRound
      ⟨frame (arrLocals a { x with idx := j } sg g s L.length off δ), μ'⟩ 37 fun σ' =>
      ∃ (x' : ArrScratch) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a { x' with idx := j } sg g s L.length off δ), μ''⟩ ∧
        PlaceInv μ μ'' a.y off δ a.Mo K val (j + 1) := by
  (((obtain ⟨⟩ := _root_.id H; obtain ⟨⟩ := _root_.id H.bucket; obtain ⟨⟩ := _root_.id H.bucket.ok))
                                   )
  have hcells := H.bucket.ok.cells
  simp only [collNeed] at hcells
  have hjK : j < K.length := hlen ▸ hj
  have hkey_lt := hlt _ (List.getElem_mem hjK)
  have hout : ∀ b, (b < a.y ∨ a.y + ylen ≤ b) → μ' b = μ b := fun b hb =>
    inv.rest b fun ⟨r, hr, hEq⟩ => by omega
  have hkey : μ' (a.fr + j) = (K[j] : ℕ) := (hout _ (by omega)).trans (counted.keys.getElem hjK)
  have hcount : μ' (a.cnt + K[j]) = (K.count K[j] : ℤ) :=
    (hout _ (by omega)).trans (counted.counts _ (by omega))
  have hread : μ' (s + j) = L[j] := (hout _ (by omega)).trans (hL j hj)
  have hV : |sg * L[j]| ≤ (a.V : ℤ) := by
    rcases H.sign with rfl | rfl <;> simpa using H.bucket.bounded.getElem hj
  have hprod := abs_le.1 hV
  have habs := abs_mul sg L[j]
  have hg' := abs_le.1 (le_refl |g|)
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen K[j] ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hkey]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hkey] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkey] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                          )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.iteIffThen (K.count K[j] = 1) (fun hone => ?_) (fun hmany => ?_) ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hcount]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hcount] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount] <;> omega))
       all_goals
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_))
                                                    )
  ·
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen (a.y + 4 * K[j] + off : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                       )
    ((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (sg * L[j] + g) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                   _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                   hread]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hread] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                        )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (a.y + 4 * K[j] + off) (sg * L[j] + g) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                     )
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.storeToThen (a.y + 4 * K[j] + off + δ) (sg * L[j] + g) ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                         )
    refine ⟨⟨j, (a.y + 4 * K[j] + off : ℕ), K[j], sg * L[j] + g, x.res, x.fr2⟩, _, rfl, ?_⟩
    rw [hval j hjK hj hone]
    exact inv.succ_one hjK hkey_lt hone H.dist
  · ((with_unfolding_none refine _root_.Light.Ends.skip ?_)
             )
    exact ⟨{ x with key := K[j] }, μ', rfl, inv.succ_many hjK hmany⟩
theorem placeLoop_ends (H : PassPre lim μ₀ d a sg g s off δ cap ylen L) (hlen : K.length = L.length)
    (hlt : ∀ q ∈ K, q < a.Mo) (counted : Counted μ a.fr a.cnt cap K) (hL : Seg μ s L)
    (hval : ∀ j (hK : j < K.length) (hj : j < L.length), K.count K[j] = 1 →
      sg * L[j] + g = val K[j]) (x : ArrScratch) :
    Ends lim P d placeLoop ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩ (45 * L.length + 6)
      fun σ' => ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        PlaceInv μ μ' a.y off δ a.Mo K val L.length := by
  have hword := sq_add_le_word H.bucket.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  exact Ends.forShape
    (fun j x' μ' => ⟨frame (arrLocals a { x' with idx := j } sg g s L.length off δ), μ'⟩)
    (fun j μ' => PlaceInv μ μ' a.y off δ a.Mo K val j) L.length 37 x .zero
    (fun j x' μ' hj inv => placeRound_ends H hlen hlt counted hL hval x' hj inv)
    (fun x' μ' inv => ⟨_, μ', rfl, inv⟩)
theorem place_ends {pResid pTally : ℕ} (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a sg g s off δ cap ylen L)
    (hval : ∀ j (hj : j < L.length),
      (keys a.Mo (L.map (sg * ·))).count ((sg * L[j]) % (a.Mo : ℤ)).toNat = 1 →
        sg * L[j] + g = val ((sg * L[j]) % (a.Mo : ℤ)).toNat) (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ), σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        (∀ r < a.Mo, ∀ e, (e = 0 ∨ e = δ) → μ' (a.y + 4 * r + off + e) =
          if (keys a.Mo (L.map (sg * ·))).count r = 1 then val r
          else μ (a.y + 4 * r + off + e)) ∧
        SameOn (fun b => b < a.fr ∧ ¬ PlaceCell a.y off δ a.Mo b) μ μ' := by
  have C := H.bucket
  simp only [tPlace]
  have hlen : (keys a.Mo (L.map (sg * ·))).length = L.length := by simp
  have hlt := keys_lt C.modulus_pos (L.map (sg * ·))
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  (((obtain ⟨⟩ := _root_.id H; obtain ⟨⟩ := _root_.id C; obtain ⟨⟩ := _root_.id C.ok))
                     )
  have hcells := C.ok.cells
  have hdepth := C.ok.depth
  simp only [collNeed] at hcells hdepth
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (a.fr + L.length : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         | refine _root_.Light.Ends.callToThen ((C.resid_meets hR H.sign) _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen (C.resid_meets hR H.sign) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro - μ₁
               ⟨hkeys, kept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                              )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen ((C.count_meets hT hlen hlt hkeys kept₁) _ (by omega)) ?_ ?_
               ?_ ?_
         | refine _root_.Light.Ends.callToThen (C.count_meets hT hlen hlt hkeys kept₁) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro res μ₂
               ⟨counted, kept₂⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (placeLoop_ends H hlen hlt counted (C.list.of_sameOn kept₂ fun i hi => by omega)
                 (fun j _ hj hone => by simpa [keys] using hval j hj (by simpa [keys] using hone))
                 { x with res := res, fr2 := (a.fr + L.length : ℕ) })
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (placeLoop_ends H hlen hlt counted (C.list.of_sameOn kept₂ fun i hi => by omega)
                 (fun j _ hj hone => by simpa [keys] using hval j hj (by simpa [keys] using hone))
                 { x with res := res, fr2 := (a.fr + L.length : ℕ) })
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨x₃, μ₃, rfl, inv⟩))
                                                                                 )
  have same₃ : SameOutside μ₂ μ₃ a.y ylen := SameOn.mono inv.rest fun b hb hcell => by
    have := H.placeCell_lt hcell
    omega
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((C.uncount_meets hT hlen hlt (counted.of_sameOutside same₃ H.belowArr H.apartTable)) _
                 (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (C.uncount_meets hT hlen hlt (counted.of_sameOutside same₃ H.belowArr H.apartTable)) ?_
               ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro res' μ₄ ⟨zero₄, same₄⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                              )
  refine ⟨{ x₃ with res := res' }, μ₄, rfl, fun r hr e he => ?_, ?_⟩
  · have hcell := H.placeCell_lt (b := a.y + 4 * r + off + e) ⟨r, hr, by omega⟩
    rw [← hlen] at inv
    rw [same₄ _ (by omega), inv.done hr he, kept₂ _ (by omega)]
  · exact sameOn_of_zeroAt ((kept₂.then inv.rest fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
      fun b hb => ⟨hb, hb.2⟩) C.zero zero₄
theorem place_arr {pResid pTally : ℕ} (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a sg g s off δ cap ylen L) (hnd : L.Nodup) {pd : ℤ}
    (hpad : ∀ r < a.Mo, ∀ e, (e = 0 ∨ e = δ) → μ (a.y + 4 * r + off + e) = pd + g)
    (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ), σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        (∀ r < a.Mo, ∀ e, (e = 0 ∨ e = δ) → μ' (a.y + 4 * r + off + e) =
          arr (L.map (sg * ·)).toFinset a.Mo pd r + g) ∧
        SameOn (fun b => b < a.fr ∧ ¬ PlaceCell a.y off δ a.Mo b) μ μ' := by
  have hM := H.bucket.modulus_pos
  have hnd' : (L.map (sg * ·)).Nodup := hnd.map fun u w huw => by
    rcases H.sign with rfl | rfl <;> simpa using huw
  refine (place_ends hR hT H (val := fun r => arr (L.map (sg * ·)).toFinset a.Mo pd r + g)
    (fun j hj hone => ?_) x).mono le_rfl ?_
  · have h := arr_of_count_eq_one hM hnd' pd (j := j) (by simpa using hj)
    simp only [List.getElem_map] at h
    rw [h hone]
  · rintro _ ⟨x', μ', rfl, hcells, hrest⟩
    refine ⟨x', μ', rfl, fun r hr e he => ?_, hrest⟩
    rw [hcells r hr e he]
    split_ifs with hone
    · rfl
    · rw [arr_of_count_ne_one hM hnd' pd hone, hpad r hr e he]
end pass
abbrev KeptCol (μ μ' : ℕ → ℤ) (fr y c t : ℕ) : Prop :=
  SameOn (fun b => b < fr ∧ ∀ i < c, b ≠ y + 4 * i + t) μ μ'
theorem KeptCol.cell {μ μ' : ℕ → ℤ} {fr y c t : ℕ} (h : KeptCol μ μ' fr y c t) {i t' : ℕ}
    (hb : y + 4 * i + t' < fr) (ht : t < 4 := by omega) (ht' : t' < 4 := by omega)
    (hne : t' ≠ t := by omega) : μ' (y + 4 * i + t') = μ (y + 4 * i + t') :=
  h _ ⟨hb, fun _ _ => by omega⟩
theorem KeptCol.keptBut {μ μ' μ'' : ℕ → ℤ} {fr y c t : ℕ} (h : KeptCol μ' μ'' fr y c t)
    (hk : KeptBut μ μ' fr y (4 * c)) (ht : t < 4 := by omega) : KeptBut μ μ'' fr y (4 * c) :=
  hk.then h fun b hb => ⟨hb, hb.1, fun i hi => by have := hb.2; omega⟩
section column
variable {μ : ℕ → ℤ} {a : ArrArgs} {g pd : ℤ} {s off cap c : ℕ} {L : List ℤ} {pResid pTally : ℕ}
theorem place_col (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a 1 g s off 0 cap (4 * c) L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = pd + g) (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x 1 g s L.length off 0), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ), σ' = ⟨frame (arrLocals a x' 1 g s L.length off 0), μ'⟩ ∧
        (∀ i < c, μ' (a.y + 4 * i + off) = arr L.toFinset a.Mo pd i + g) ∧
        KeptCol μ μ' a.fr a.y c off := by
  (((obtain ⟨⟩ := _root_.id H))
              )
  refine (place_arr hR hT H hnd (pd := pd) (fun r hr e he => ?_) x).mono le_rfl ?_
  · obtain rfl : e = 0 := by omega
    exact hpad r (by omega)
  rintro _ ⟨x', μ', rfl, hcells, hrest⟩
  refine ⟨x', μ', rfl, fun i hi => ?_, SameOn.mono hrest fun b hb => ⟨hb.1, ?_⟩⟩
  · by_cases hiM : i < a.Mo
    · simpa using hcells i hiM 0 (Or.inl rfl)
    · rw [hrest _ ⟨by omega, fun ⟨r, hr, hEq⟩ => by omega⟩,
        arr_of_le H.bucket.modulus_pos _ _ (by omega), hpad i hi]
  · rintro ⟨r, hr, hEq⟩
    exact hb.2 r (by omega) (by omega)
theorem place_colZ (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a (-1) g s off (4 * a.Mo) cap (4 * c) L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = -(2 * a.V + 1) + g) (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally)
      ⟨frame (arrLocals a x (-1) g s L.length off (4 * a.Mo)), μ⟩
      (tPlace L.length a.V) fun σ' =>
      (∀ i < c, σ'.mem (a.y + 4 * i + off) = arrZ L.toFinset a.Mo a.V i + g) ∧
        KeptCol μ σ'.mem a.fr a.y c off := by
  (((obtain ⟨⟩ := _root_.id H))
              )
  have himage : (L.map (-1 * ·)).toFinset = L.toFinset.image fun u => -u := by
    ext u
    simp
  refine (place_arr hR hT H hnd (pd := -(2 * a.V + 1)) (fun r hr e he => ?_) x).mono le_rfl ?_
  · rcases he with rfl | rfl
    · exact hpad r (by omega)
    · rw [show a.y + 4 * r + off + 4 * a.Mo = a.y + 4 * (r + a.Mo) + off by ring]
      exact hpad _ (by omega)
  rintro _ ⟨x', μ', rfl, hcells, hrest⟩
  rw [himage] at hcells
  refine ⟨fun i hi => ?_, SameOn.mono hrest fun b hb => ⟨hb.1, ?_⟩⟩
  · change μ' (a.y + 4 * i + off) = _
    unfold arrZ pad
    by_cases hiM : i < a.Mo
    · rw [if_pos (by omega), Nat.mod_eq_of_lt hiM]
      simpa using hcells i hiM 0 (Or.inl rfl)
    · by_cases hi2 : i < 2 * a.Mo
      · have h := hcells (i - a.Mo) (by omega) (4 * a.Mo) (Or.inr rfl)
        rw [show a.y + 4 * (i - a.Mo) + off + 4 * a.Mo = a.y + 4 * i + off by omega] at h
        rw [if_pos hi2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        simpa using h
      · rw [if_neg hi2, hrest _ ⟨by omega, fun ⟨r, hr, hEq⟩ => by omega⟩, hpad i hi]
  · rintro ⟨r, hr, hEq | hEq⟩
    · exact hb.2 r (by omega) hEq
    · exact hb.2 (r + a.Mo) (by omega) (by omega)
end column
section routine
variable {μ μ' : ℕ → ℤ} {n : ℕ} {a : ArrArgs} {s : ℕ} {L : List ℤ} {pResid pTally : ℕ}
theorem ArrPre.keptBut (h : ArrPre lim μ d n a)
    (hk : KeptBut μ μ' a.fr a.y (4 * (2 * (a.m * a.m)))) : ArrPre lim μ' d n a := by
  (((obtain ⟨⟩ := _root_.id h))
              )
  exact { h with zero := fun q hq => (hk _ (by omega)).trans (h.zero q hq) }
theorem ArrSet.keptBut (h : ArrSet μ n a s L)
    (hk : KeptBut μ μ' a.fr a.y (4 * (2 * (a.m * a.m)))) : ArrSet μ' n a s L := by
  (((obtain ⟨⟩ := _root_.id h))
              )
  exact { h with list := h.list.of_sameOn hk fun i hi => by omega }
theorem ArrPre.word_le (h : ArrPre lim μ d n a) : 64 * ((a.V : ℤ) + 1) ≤ lim.word := by
  simpa using mul_le_word (x := 1) (y := 1) (z := 64 * (a.V + 1)) h.ok.word
    (Nat.one_le_pow _ _ (by omega)) (by omega) le_rfl
theorem ArrPre.pass (h : ArrPre lim μ d n a) (hS : ArrSet μ n a s L) {sg g : ℤ} {off δ : ℕ}
    (hsg : sg = 1 ∨ sg = -1) (hoff : off < 4) (hδ : δ = 0 ∨ δ = 4 * a.Mo)
    (hg₀ : 0 ≤ g) (hg : g ≤ 32 * ((a.V : ℤ) + 1)) :
    PassPre lim μ d a sg g s off δ (a.m * a.m) (4 * (2 * (a.m * a.m))) L := by
  have hM := h.modulus_le
  have hword := h.word_le
  have hle := hS.le
  have habs := abs_of_nonneg hg₀
  exact
    { bucket :=
        { modulus_pos := h.modulus_pos
          modulus_le := hM
          bounded := hS.bounded
          list := hS.list
          zero := h.zero
          belowList := hS.below
          belowTable := h.belowTable
          apart := hS.apartTable
          ok := h.ok.mono (wordNeed_mono hle hM) (by simp only [collNeed, nodeArrayNeed]; omega)
            le_rfl }
      sign := hsg
      belowArr := h.belowArr
      apartSet := hS.apartArr
      apartTable := h.apartTable
      room := by omega
      off_lt := hoff
      dist := by omega
      value_le := by omega }
theorem arrConsts_ends (h : ArrPre lim μ d n a) :
    Ends lim P d arrConsts
      ⟨frame [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr], μ⟩ 38
      fun σ' => σ' = ⟨frame (arrLocals a ⟨0, 0, 0, 0, 0, 0⟩ 0 0 0 0 0 0), μ⟩ := by
  have hword := h.word_le
  (((obtain ⟨⟩ := _root_.id h; obtain ⟨⟩ := _root_.id h.ok))
                   )
  have hnonneg : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  have habs : |6 * (a.V : ℤ) + 4| = 6 * a.V + 4 := abs_of_nonneg (by positivity)
  have hgroups : 8 * ((a.m : ℤ) * a.m) ≤ lim.space := by
    have : 8 * (a.m * a.m) ≤ lim.space := by omega
    exact_mod_cast this
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (2 * a.V + 1) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (6 * a.V + 4) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (2 * (a.m * a.m) : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (padVal a.V 0) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 padVal]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [padVal] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, padVal] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                      )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (padVal a.V 1) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 padVal]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [padVal] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, padVal] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                      )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (padVal a.V 2) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 padVal]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [padVal] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, padVal] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                      )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (padVal a.V 3) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 padVal]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [padVal] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, padVal] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                      )
  rfl
theorem arrPass₁_ends (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a) (hS : ArrSet μ n a a.s₁ L) (hl : a.l₁ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 1) = padVal a.V 1) {x : ArrScratch}
    {sg g : ℤ} {s len off δ : ℕ} :
    Ends lim P d (arrPass₁ pResid pTally) ⟨frame (arrLocals a x sg g s len off δ), μ⟩
      (12 + tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' 1 (6 * a.V + 4) a.s₁ L.length 1 0), μ'⟩ ∧
        (∀ i < 2 * (a.m * a.m), μ' (a.y + 4 * i + 1) =
          arr L.toFinset a.Mo (2 * a.V + 1) i + (6 * a.V + 4)) ∧
        KeptCol μ μ' a.fr a.y (2 * (a.m * a.m)) 1 := by
  have hword := h.word_le
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (6 * a.V + 4) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen a.s₁ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
               )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen L.length ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  ((focus
       (refine
           _root_.Light.Ends.pieceLast
             (place_col hR hT
               (h.pass hS (Or.inl rfl) (by omega) (Or.inl rfl) (by positivity) (by omega)) hS.nodup
               (pd := 2 * a.V + 1) (fun i hi => by rw [hpad i hi]; simp [padVal]) x)
             (fun _ macro_local_1 => macro_local_1) ?_;
         on_goal -1 =>
           ((first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega))))))
                                                    )
theorem arrPass₂_ends (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a) (hS : ArrSet μ n a a.s₂ L) (hl : a.l₂ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 2) = padVal a.V 2) {x : ArrScratch}
    {g : ℤ} {s len off : ℕ} :
    Ends lim P d (arrPass₂ pResid pTally) ⟨frame (arrLocals a x 1 g s len off 0), μ⟩
      (10 + tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' 1 (3 * (6 * a.V + 4)) a.s₂ L.length 2 0), μ'⟩ ∧
        (∀ i < 2 * (a.m * a.m), μ' (a.y + 4 * i + 2) =
          arr L.toFinset a.Mo (2 * a.V + 1) i + 3 * (6 * a.V + 4)) ∧
        KeptCol μ μ' a.fr a.y (2 * (a.m * a.m)) 2 := by
  have hword := h.word_le
  have habs : |6 * (a.V : ℤ) + 4| = 6 * a.V + 4 := abs_of_nonneg (by positivity)
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (3 * (6 * a.V + 4)) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                              )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen a.s₂ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
               )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen L.length ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (2 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  ((focus
       (refine
           _root_.Light.Ends.pieceLast
             (place_col hR hT
               (h.pass hS (Or.inl rfl) (by omega) (Or.inl rfl) (by positivity) (by omega)) hS.nodup
               (pd := 2 * a.V + 1) (fun i hi => by rw [hpad i hi]; simp [padVal]) x)
             (fun _ macro_local_1 => macro_local_1) ?_;
         on_goal -1 =>
           ((first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega))))))
                                                    )
theorem arrPass₃_ends (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a) (hS : ArrSet μ n a a.s₃ L) (hl : a.l₃ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 3) = padVal a.V 3) {x : ArrScratch}
    {sg g : ℤ} {s len off δ : ℕ} :
    Ends lim P d (arrPass₃ pResid pTally) ⟨frame (arrLocals a x sg g s len off δ), μ⟩
      (18 + tPlace L.length a.V) fun σ' =>
      (∀ i < 2 * (a.m * a.m), σ'.mem (a.y + 4 * i + 3) =
        arrZ L.toFinset a.Mo a.V i + 4 * (6 * a.V + 4)) ∧
      KeptCol μ σ'.mem a.fr a.y (2 * (a.m * a.m)) 3 := by
  have hword := h.word_le
  have habs : |6 * (a.V : ℤ) + 4| = 6 * a.V + 4 := abs_of_nonneg (by positivity)
  (((obtain ⟨⟩ := _root_.id h; obtain ⟨⟩ := _root_.id h.ok))
                   )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (-1) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
               )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (4 * (6 * a.V + 4)) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                              )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen a.s₃ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
               )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen L.length ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hl]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hl] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (3 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (4 * a.Mo : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                         )
  ((focus
       (refine
           _root_.Light.Ends.pieceLast
             (place_colZ hR hT
               (h.pass hS (Or.inr rfl) (by omega) (Or.inr rfl) (by positivity) (by omega)) hS.nodup
               (fun i hi => by rw [hpad i hi]; simp [padVal]) x)
             (fun _ macro_local_1 => macro_local_1) ?_;
         on_goal -1 =>
           ((first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega))))))
                                                                                         )
theorem oneArray_of_cells {ν : Node} {V y c : ℕ} (h₀ : ∀ i < c, μ (y + 4 * i + 0) = padVal V 0)
    (h₁ : ∀ i < c, μ (y + 4 * i + 1) = arr ν.S₁ ν.M (2 * V + 1) i + (6 * V + 4))
    (h₂ : ∀ i < c, μ (y + 4 * i + 2) = arr ν.S₂ ν.M (2 * V + 1) i + 3 * (6 * V + 4))
    (h₃ : ∀ i < c, μ (y + 4 * i + 3) = arrZ ν.S₃ ν.M V i + 4 * (6 * V + 4)) :
    ∀ u < 4 * c, μ (y + u) = ν.oneArray V u := by
  intro u hu
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 4 ∧ u = 4 * i + t :=
    ⟨u / 4, u % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod u 4).symm⟩
  obtain ⟨c₀, c₁, c₂, c₃⟩ := oneArray_cells ν V i
  rw [← Nat.add_assoc]
  interval_cases t
  · rw [h₀ i (by omega), Nat.add_zero, c₀]
    simp [padVal]
  · rw [h₁ i (by omega), c₁]
  · rw [h₂ i (by omega), c₂]
  · rw [h₃ i (by omega), c₃]
theorem nodeArrayBody_ends {L₁ L₂ L₃ : List ℤ} (hR : ResidSpec lim P pResid)
    (hT : TallySpec lim P pTally) (h : ArrPre lim μ d n a) (hS₁ : ArrSet μ n a a.s₁ L₁)
    (hS₂ : ArrSet μ n a a.s₂ L₂) (hS₃ : ArrSet μ n a a.s₃ L₃) (hl₁ : a.l₁ = L₁.length)
    (hl₂ : a.l₂ = L₂.length) (hl₃ : a.l₃ = L₃.length) :
    Ends lim P d (nodeArrayBody pResid pTally)
      ⟨frame [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr], μ⟩
      (42 * (2 * (a.m * a.m)) + tPlace L₁.length a.V + tPlace L₂.length a.V + tPlace L₃.length a.V
        + 84) fun σ' =>
      (∀ u < 4 * (2 * (a.m * a.m)), σ'.mem (a.y + u) =
        Node.oneArray ⟨L₁.toFinset, L₂.toFinset, L₃.toFinset, a.Mo⟩ a.V u) ∧
      KeptBut μ σ'.mem a.fr a.y (4 * (2 * (a.m * a.m))) := by
  (((obtain ⟨⟩ := _root_.id h; obtain ⟨⟩ := _root_.id h.ok))
                   )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (arrConsts_ends h) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (arrConsts_ends h) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ rfl))
                                          )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (pad_ends h.ok.space (by omega)) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (pad_ends h.ok.space (by omega)) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨μ₀, ⟨hpad, same₀⟩, rfl⟩))
                                                                             )
  have kept₀ : KeptBut μ μ₀ a.fr a.y (4 * (2 * (a.m * a.m))) := SameOn.mono same₀ fun _ hb => hb.2
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (arrPass₁_ends hR hT (h.keptBut kept₀) (hS₁.keptBut kept₀) hl₁ fun i hi =>
                 hpad i hi 1 (by omega))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (arrPass₁_ends hR hT (h.keptBut kept₀) (hS₁.keptBut kept₀) hl₁ fun i hi =>
                 hpad i hi 1 (by omega))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨x₁, μ₁, rfl, col₁, same₁⟩))
                                                                        )
  have kept₁ := same₁.keptBut kept₀
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (arrPass₂_ends hR hT (h.keptBut kept₁) (hS₂.keptBut kept₁) hl₂ fun i hi =>
                 (same₁.cell (by omega)).trans (hpad i hi 2 (by omega)))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (arrPass₂_ends hR hT (h.keptBut kept₁) (hS₂.keptBut kept₁) hl₂ fun i hi =>
                 (same₁.cell (by omega)).trans (hpad i hi 2 (by omega)))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨x₂, μ₂, rfl, col₂, same₂⟩))
                                    )
  have kept₂ := same₂.keptBut kept₁
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (arrPass₃_ends hR hT (h.keptBut kept₂) (hS₃.keptBut kept₂) hl₃ fun i hi =>
                 (same₂.cell (by omega)).trans
                   ((same₁.cell (by omega)).trans (hpad i hi 3 (by omega))))
               ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (arrPass₃_ends hR hT (h.keptBut kept₂) (hS₃.keptBut kept₂) hl₃ fun i hi =>
                 (same₂.cell (by omega)).trans
                   ((same₁.cell (by omega)).trans (hpad i hi 3 (by omega))))
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro ⟨_, μ₃⟩
             ⟨col₃, same₃⟩
                 ))
                                                          )
  refine ⟨oneArray_of_cells (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) col₃,
    same₃.keptBut kept₂⟩
  · exact (same₃.cell (by omega)).trans
      ((same₂.cell (by omega)).trans
        ((same₁.cell (by omega)).trans (hpad i hi 0 (by omega))))
  · exact (same₃.cell (by omega)).trans
      ((same₂.cell (by omega)).trans (col₁ i hi))
  · exact (same₃.cell (by omega)).trans (col₂ i hi)
end routine
theorem nodeArray_spec {p pResid pTally : ℕ} (hp : P[p]? = some (nodeArrayBody pResid pTally))
    (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally) : NodeArraySpec lim P p := by
  rintro ⟨⟨fr, n, V, m, np, pr, cnt⟩, ⟨s₁, l₁, S₁⟩, ⟨s₂, l₂, S₂⟩, ⟨s₃, l₃, S₃⟩⟩ Mo y μ
    ⟨henv, h₁, h₂, h₃⟩ hM hMm ⟨hy, ay₁, ay₂, ay₃, ayc⟩ d hok
  obtain ⟨L₁, rfl, seg₁, nodup₁, rfl⟩ : SetAt μ s₁ l₁ S₁ := h₁.set
  obtain ⟨L₂, rfl, seg₂, nodup₂, rfl⟩ : SetAt μ s₂ l₂ S₂ := h₂.set
  obtain ⟨L₃, rfl, seg₃, nodup₃, rfl⟩ : SetAt μ s₃ l₃ S₃ := h₃.set
  have hsq : 8 * m ^ 2 = 4 * (2 * (m * m)) := by ring
  dsimp only at hy ay₁ ay₂ ay₃ ayc hM hMm hok ⊢
  rw [hsq] at hy ay₁ ay₂ ay₃ ayc ⊢
  refine .of_body hp ((nodeArrayBody_ends (n := n)
    (a := ⟨Mo, s₁, L₁.length, s₂, L₂.length, s₃, L₃.length, V, m, y, cnt, fr⟩) hR hT
    ⟨hM, hMm, henv.zero, henv.belowCnt, hy, ayc, hok⟩
    ⟨seg₁, nodup₁, fun x hx => h₁.bdd x (List.mem_toFinset.2 hx), h₁.le, h₁.below, h₁.apart, ay₁⟩
    ⟨seg₂, nodup₂, fun x hx => h₂.bdd x (List.mem_toFinset.2 hx), h₂.le, h₂.below, h₂.apart, ay₂⟩
    ⟨seg₃, nodup₃, fun x hx => h₃.bdd x (List.mem_toFinset.2 hx), h₃.le, h₃.below, h₃.apart, ay₃⟩
    rfl rfl rfl).mono ?_ fun _ h => h)
  simp only [tNodeArray, tPlace, sq]
  omega
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
variable {lim : Limits} {P : Program}
private theorem five_mul_Lam_le_wPar (n V : ℕ) : 5 * Lam V ≤ wPar n V :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
private theorem wPar_succ_le_mPar (n V : ℕ) : wPar n V + 1 ≤ mPar n V :=
  Nat.le_mul_of_pos_right _ (by omega)
private theorem log_wPar_le_mPar (n V : ℕ) : 2 * Nat.log 2 (wPar n V + 1) + 4 ≤ mPar n V :=
  Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
private theorem height_le (n : ℕ) : height n ≤ Nat.log 2 n + 2 :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
namespace Params
end Params
theorem params_spec {p pLog2 pClog2 pSqrt : ℕ} (hP : P[p]? = some (paramsBody pLog2 pClog2 pSqrt))
    (hL : Log2Spec lim P pLog2) (hC : Clog2Spec lim P pClog2) (hS : P[pSqrt]? = some sqrtBody) :
    ParamsSpec lim P p := by
  intro d n V out μ hout hw hword hdep
  refine Meets.of_body hP ?_
  have eΛ : (Lam V : ℤ) = Nat.log 2 (2 * V) + 1 := by simp [Lam]
  have ew : 5 * (Lam V : ℤ) * ((Nat.sqrt n : ℤ) + 1) = wPar n V := by simp [wPar]
  have em : ((wPar n V : ℤ) + 1) * (2 * (Nat.log 2 (wPar n V + 1) : ℤ) + 4) = mPar n V := by
    simp [mPar]
  have eh : height n = Nat.clog 2 (Nat.log 2 n + 2) := rfl
  have ef : 3 * (height n : ℤ) - 2 = fuel n := by have := height_pos n; simp only [fuel]; omega
  have := five_mul_Lam_le_wPar n V
  have := wPar_succ_le_mPar n V
  have := log_wPar_le_mPar n V
  have := height_le n
  have := Nat.sqrt_le_self n
  have := Nat.log_le_self 2 n
  have : mPar n V + 1 ≤ (mPar n V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hword' : ((8 * (mPar n V + 1) + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
  push_cast at hword'
  unfold tParams paramsBody
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen ((hL (d + 1) (2 * V) μ (by push_cast; omega)) _ (by omega))
               ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen (hL (d + 1) (2 * V) μ (by push_cast; omega)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ
               ⟨rfl, rfl⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (Lam V)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((sqrt_meets (K := n) hS μ (by push_cast; omega)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (sqrt_meets (K := n) hS μ (by push_cast; omega)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ
               ⟨rfl, rfl⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (wPar n V + 1 : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 ew]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [ew] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ew] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                      )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hL (d + 1) (wPar n V + 1) μ (by push_cast; omega)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (hL (d + 1) (wPar n V + 1) μ (by push_cast; omega)) ?_ ?_ ?_
               ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ
               ⟨rfl, rfl⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                   )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (mPar n V) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 em]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [em] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, em] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                              )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         | refine _root_.Light.Ends.callToThen ((hL (d + 1) n μ (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen (hL (d + 1) n μ (by omega)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ
               ⟨rfl, rfl⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                           )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hC (d + 1) (Nat.log 2 n + 2) μ (by push_cast; omega)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (hC (d + 1) (Nat.log 2 n + 2) μ (by push_cast; omega)) ?_ ?_
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ
               ⟨rfl, rfl⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                      )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (fuel n)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                   )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen out (Lam V) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (out + 1) (mPar n V) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                 )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (out + 2) (fuel n) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                               )
  refine ⟨?_, ?_⟩
  · simp [seg_cons]
  · intro c hc
    simp [show c ≠ out by omega, show c ≠ out + 1 by omega, show c ≠ out + 2 by omega]
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Prep
end Prep
abbrev prepFrame (a : Map) (V x : ℕ) : List ℤ :=
  [a.n, V, a.Λ, a.m, x, a.b, a.pr, ((a.m * a.m : ℕ) : ℤ), a.cnt, a.srt, a.val, a.mul, a.bt, a.A,
    a.tw, a.one, a.top]
theorem prepAddr_runs (a : Map) (V x : ℕ) (μ : ℕ → ℤ) (htop : (a.top : ℤ) ≤ lim.word)
    (hword : (6 : ℤ) ≤ lim.word) :
    prepAddr.Runs lim ⟨frame [a.n, V, a.Λ, a.m, x, a.b], μ⟩ (· = ⟨frame (prepFrame a V x), μ⟩) := by
  have hmap := a.layout
  have : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  have : (0 : ℤ) ≤ (a.n : ℤ) * a.Λ := by positivity
  exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, prepAddr] <;> omega))
                                ),
    by simp [prepAddr, update_frame_setLocal, prepFrame, Map.top, Map.one, Map.tw, Map.A, Map.bt,
      Map.mul, Map.val, Map.srt, Map.cnt, Map.pr]⟩
private theorem ok_primes {n V Λ m fr : ℕ} (h : (prepNeed n V Λ m).Ok lim fr d) :
    (primesNeed m).Ok lim fr (d + 1) := by
  have : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine h.mono ?_ ?_ ?_ <;> simp only [primesNeed, prepNeed] <;> omega
private theorem ok_sort {n V Λ m fr : ℕ} (h : (prepNeed n V Λ m).Ok lim fr d) :
    (sortNeed n V).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [sortNeed, prepNeed] <;> omega
theorem prepTables_ends {pPrimes pFill : ℕ} (hPr : PrimesSpec lim P pPrimes)
    (hFi : P[pFill]? = some fillBody) (a : Map) {V x : ℕ} {μ : ℕ → ℤ}
    (hok : (prepNeed a.n V a.Λ a.m).Ok lim a.top d) :
    Ends lim P d (prepTables pPrimes pFill) ⟨frame (prepFrame a V x), μ⟩
      (10 + tPrimes a.m + (13 * (a.m * a.m) + 6)) fun σ' => ∃ (μ' : ℕ → ℤ) (r : ℤ),
        σ' = ⟨frame (prepFrame a V x ++ [(#(Nat.primesLE a.m) : ℤ), r]), μ'⟩ ∧
        PrimesAt μ' a.pr #(Nat.primesLE a.m) a.m ∧ ZeroAt μ' a.cnt (a.m * a.m) ∧
        SameOn (fun c => c < a.top ∧ Outside a.pr (a.m + a.m * a.m) c) μ μ' := by
  have hmap := a.layout
  have hw := hok.space
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [prepNeed] at hcells hword hdepth
  push_cast at hword
  have hnp := Nat.card_primesLE_le a.m
  unfold prepTables
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hPr (d + 1) a.top a.m a.pr μ (by omega) (ok_primes hok)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (hPr (d + 1) a.top a.m a.pr μ (by omega) (ok_primes hok)) ?_
               ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁
               ⟨rfl, hprimes, hkept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                   )
  refine Ends.callTo
    (fill_meets (μ := μ₁) (dst := a.cnt) (n := a.m * a.m) (x := 0) hFi hw (by omega)) ?_
  rintro r μ₂ ⟨hzero, hkept₂⟩
  refine ⟨μ₂, r, rfl,
    ⟨rfl, hprimes.of_sameOutside hkept₂ (.inl (by rw [List.length_map, length_sort]; omega))⟩,
    fun i hi => ?_, hkept₁.then hkept₂ fun c hc => ⟨⟨hc.1, by omega⟩, by omega⟩⟩
  rw [hzero i (by simpa using hi)]
  simp
theorem prepSorted_ends {pCopy pSort : ℕ} (hCo : P[pCopy]? = some copyBody)
    (hSo : SortSpec lim P pSort) {a : Map} {V x : ℕ} {X : List ℤ} (C : Prep.Ctx lim d a V x X)
    {μ : ℕ → ℤ} (hseg : Seg μ x X) (np r : ℤ) :
    Ends lim P d (prepSorted pCopy pSort) ⟨frame (prepFrame a V x ++ [np, r]), μ⟩
      (10 + (16 * a.n + 6) + tSort a.n) fun σ' => ∃ (μ' : ℕ → ℤ) (r' : ℤ) (Ls : List ℤ),
        σ' = ⟨frame (prepFrame a V x ++ [np, r']), μ'⟩ ∧ Seg μ' a.srt Ls ∧ Ls.Perm X ∧
        Ls.Pairwise (· ≤ ·) ∧ SameOn (· < a.srt) μ μ' := by
  have hmap := a.layout
  have hlen := C.len
  have hbelow := C.below
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hdepth := C.ok.depth
  simp only [prepNeed] at hcells hdepth
  have htime : tSort X.length = tSort a.n := by rw [hlen]
  unfold prepSorted
  have hroom : a.srt + X.length ≤ lim.space := by omega
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((copy_meets (μ := μ) (src := x) (dst := a.srt) (n := X.length) hCo hw (by omega) hroom
                   (.inl (by omega)))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (copy_meets (μ := μ) (src := x) (dst := a.srt) (n := X.length) hCo hw (by omega) hroom
                 (.inl (by omega)))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨hcells₁, hkept₁⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                  )
  have hcopy : Seg μ₁ a.srt X := fun i hi => (hcells₁ i hi).trans (hseg i hi)
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hSo (d + 1) a.top a.srt V X μ₁ hcopy C.bounded (by omega) (hlen ▸ ok_sort C.ok)) _
                 (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hSo (d + 1) a.top a.srt V X μ₁ hcopy C.bounded (by omega) (hlen ▸ ok_sort C.ok)) ?_ ?_
               ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro r' μ₂ ⟨⟨Ls, hLs, hperm, hsorted⟩, hkept₂⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                 )
  exact ⟨μ₂, r', Ls, rfl, hLs, hperm, hsorted,
    hkept₁.then hkept₂ fun c hc => ⟨by omega, by omega, by omega⟩⟩
private theorem two_mul_lt_two_pow_Lam (V : ℕ) : 2 * V < 2 ^ Lam V :=
  Nat.lt_pow_succ_log_self (by norm_num) _
private theorem two_pow_Lam_le {V : ℕ} (hV : 1 ≤ V) : 2 ^ Lam V ≤ 4 * V + 4 := by
  have := Nat.pow_log_le_self 2 (x := 2 * V) (by omega)
  rw [Lam, pow_succ]
  omega
private theorem tBits_mono {len len' : ℕ} (h : len ≤ len') (Λ : ℕ) : tBits len Λ ≤ tBits len' Λ :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) _
private theorem Distinct.Ctx.of_consecutive {μ : ℕ → ℤ} {s val mul : ℕ} {L : List ℤ}
    (hsorted : L.Pairwise (· ≤ ·)) (hseg : Seg μ s L) (hval : s + L.length ≤ val)
    (hmul : val + L.length ≤ mul) (hspace : mul + L.length ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (2 * L.length + 8 : ℤ) ≤ lim.word) :
    Distinct.Ctx lim μ s val mul L where
  sorted := hsorted
  seg := hseg
  apartVal := .inl hval
  apartMul := .inl (by omega)
  apart := .inl hmul
  spaceSrc := by omega
  spaceVal := by omega
  spaceMul := hspace
  space_le := hw
  word := hword
theorem prepValues_ends {pDistinct pBits : ℕ} (hDi : DistinctSpec lim P pDistinct)
    (hBi : BitsSpec lim P pBits) {a : Map} {V x : ℕ} {X Ls : List ℤ} (C : Prep.Ctx lim d a V x X)
    {μ : ℕ → ℤ} (hLs : Seg μ a.srt Ls) (hperm : Ls.Perm X) (hsorted : Ls.Pairwise (· ≤ ·))
    (np r : ℤ) :
    Ends lim P d (prepValues pDistinct pBits) ⟨frame (prepFrame a V x ++ [np, r]), μ⟩
      (14 + tDistinct a.n + tBits a.n a.Λ) fun σ' => ∃ (μ' : ℕ → ℤ) (r' : ℤ) (D M : List ℤ),
        σ' = ⟨frame (prepFrame a V x ++ [np, r', D.length]), μ'⟩ ∧ PrepValues μ' a V X D M ∧
        SameOn (· < a.val) μ μ' := by
  have hmap := a.layout
  have hlen : Ls.length = a.n := hperm.length_eq.trans C.len
  have hLsV : AbsLe Ls V := fun e he => C.bounded e (hperm.mem_iff.1 he)
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hword := C.ok.word
  have hdepth := C.ok.depth
  simp only [prepNeed] at hcells hword hdepth
  push_cast at hword
  have : (0 : ℤ) ≤ ((a.m : ℤ) + 1) ^ 2 := by positivity
  have htime : tDistinct Ls.length = tDistinct a.n := by rw [hlen]
  unfold prepValues
  have hctx : Distinct.Ctx lim μ a.srt a.val a.mul Ls :=
    .of_consecutive hsorted hLs (by omega) (by omega) (show a.mul + Ls.length ≤ _ by omega) hw
      (by omega)
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen ((hDi (d + 1) a.srt a.val a.mul Ls μ hctx) _ (by omega)) ?_
               ?_ ?_ ?_
         | refine _root_.Light.Ends.callToThen (hDi (d + 1) a.srt a.val a.mul Ls μ hctx) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨⟨D, rfl, hDn, hDv, hsegD, hsegM⟩, hkept₁⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                       )
  have hvalues := Values.of_perm C.len hperm hDn hDv
  have hDle := hvalues.length_le
  have hrows := Nat.mul_le_mul_right a.Λ hDle
  have hDV : AbsLe D V := fun e he =>
    hLsV e (List.mem_toFinset.1 (hDv ▸ List.mem_toFinset.2 he))
  have htime' := tBits_mono hDle a.Λ
  have hapart : Apart a.val D.length a.bt (D.length * a.Λ) := .inl (by omega)
  have hctx' : Bits.Ctx lim μ₁ a.val V a.Λ a.bt D :=
    ⟨hDV, C.digits ▸ two_mul_lt_two_pow_Lam V, C.digits ▸ two_pow_Lam_le C.bound_pos, hsegD,
      hapart, by omega, by omega, hw, by omega⟩
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hBi (d + 1) a.top a.val a.bt V a.Λ D μ₁ hctx') _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (hBi (d + 1) a.top a.val a.bt V a.Λ D μ₁ hctx') ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro r' μ₂ ⟨hsegB, hkept₂⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                      )
  exact ⟨μ₂, r', D, _, rfl, ⟨hvalues, hDV, hsegD.of_sameOutside hkept₂ (.inl (by omega)),
    hsegM.of_sameOutside hkept₂ (.inl (by simp; omega)), hsegB⟩,
    hkept₁.then hkept₂ fun c hc => ⟨⟨by omega, by omega⟩, by omega⟩⟩
theorem prepTail_ends (a : Map) {V x np nd : ℕ} {μ : ℕ → ℤ} (r : ℤ) (htop : a.top ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (5 : ℤ) ≤ lim.word) :
    Ends lim P d prepTail ⟨frame (prepFrame a V x ++ [(np : ℤ), r, nd]), μ⟩ 33 fun σ' =>
      σ'.loc 0 = nd ∧ CtxAt σ'.mem a.cx V a.m a.Λ np a.pr a.cnt ∧ σ'.mem a.one = 0 ∧
      SameOn (fun c => Outside a.b 6 c ∧ c ≠ a.one) μ σ'.mem := by
  have hmap := a.layout
  unfold prepTail
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen a.b V ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (a.b + 1) a.m ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                          )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (a.b + 2) a.Λ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                          )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (a.b + 3) np ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                         )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (a.b + 4) a.pr ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                           )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen (a.b + 5) a.cnt ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                            )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.storeToThen a.one 0 ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                    )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen nd ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
             )
  refine ⟨rfl, ?_, by simp, ?_⟩
  · have hbase : a.b ≠ a.one := by omega
    have hone : ∀ i < 6, a.b + i ≠ a.one := fun i hi => by omega
    simp [CtxAt, seg_cons, Map.cx, Nat.add_assoc, hbase, hone]
  · rintro c ⟨hoff, hone⟩
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
theorem FrontMem.of_map (a : Map) {μ : ℕ → ℤ} {V : ℕ} {D : List ℤ} (hle : D.length ≤ a.n)
    (hnodup : D.Nodup) (hbdd : AbsLe D V) (hval : Seg μ a.val D)
    (htable : Seg μ a.bt (bitTable V a.Λ D))
    (hctx : CtxAt μ a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt)
    (hprimes : PrimesAt μ a.pr #(Nat.primesLE a.m) a.m) (hzero : ZeroAt μ a.cnt (a.m * a.m)) :
    FrontMem μ (a.front V D) := by
  have hmap := a.layout
  have hnp := Nat.card_primesLE_le a.m
  have hrows := Nat.mul_le_mul_right a.Λ hle
  exact {
    lenD := rfl
    nd_le := hle
    nodup := hnodup
    bdd := fun e he => hbdd e (List.mem_toFinset.1 he)
    segVal := hval
    segBt := htable
    ctx := hctx
    primes := hprimes
    zero := hzero
    belowVal := by dsimp only [Map.front]; omega
    belowBt := by dsimp only [Map.front]; omega
    belowCx := by dsimp only [Map.front]; omega
    belowPr := by dsimp only [Map.front]; omega
    belowCnt := by dsimp only [Map.front]; omega
    belowA := by dsimp only [Map.front]; omega
    apartVal := .inr (by dsimp only [Map.front]; omega)
    apartBt := .inr (by dsimp only [Map.front]; omega)
    apartCx := .inr (by dsimp only [Map.front]; omega)
    apartPr := .inr (by dsimp only [Map.front]; omega)
    apartCnt := .inr (by dsimp only [Map.front]; omega)
    cntVal := .inr (by dsimp only [Map.front]; omega)
    cntCx := .inl (by dsimp only [Map.front]; omega)
    cntPr := .inl (by dsimp only [Map.front]; omega) }
theorem PrepValues.frontMem {a : Map} {V : ℕ} {X D M : List ℤ} {μ₁ μ₃ μ₄ : ℕ → ℤ}
    (h : PrepValues μ₃ a V X D M) (hprimes : PrimesAt μ₁ a.pr #(Nat.primesLE a.m) a.m)
    (hzero : ZeroAt μ₁ a.cnt (a.m * a.m)) (hlate : SameOn (· < a.srt) μ₁ μ₃)
    (hctx : CtxAt μ₄ a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt)
    (htail : SameOn (fun c => Outside a.b 6 c ∧ c ≠ a.one) μ₃ μ₄) :
    Seg μ₄ a.mul M ∧ FrontMem μ₄ (a.front V D) := by
  have hmap := a.layout
  have hle := h.values.length_le
  have hrows := Nat.mul_le_mul_right a.Λ hle
  have hlenM : M.length = D.length := by rw [h.values.counts, List.length_map]
  have hlenT := length_bitTable V a.Λ D
  have hnp := Nat.card_primesLE_le a.m
  have htables : SameOn (fun c => a.pr ≤ c ∧ c < a.srt) μ₁ μ₄ :=
    hlate.then htail fun c hc => ⟨hc.2, by omega, by omega⟩
  refine ⟨h.segMul.of_sameOn htail fun i hi => ⟨by omega, by omega⟩,
    .of_map a hle h.values.nodup h.bounded
      (h.segVal.of_sameOn htail fun i hi => ⟨by omega, by omega⟩)
      (h.segTable.of_sameOn htail fun i hi => ⟨by omega, by omega⟩) hctx
      ⟨rfl, hprimes.2.of_sameOn htables fun i hi => ?_⟩
      fun i hi => (htables _ ⟨by omega, by omega⟩).trans (hzero i hi)⟩
  rw [List.length_map, length_sort] at hi
  exact ⟨by omega, by omega⟩
theorem prepBody_ends {pPrimes pFill pCopy pSort pDistinct pBits : ℕ}
    (hPr : PrimesSpec lim P pPrimes) (hFi : P[pFill]? = some fillBody)
    (hCo : P[pCopy]? = some copyBody) (hSo : SortSpec lim P pSort)
    (hDi : DistinctSpec lim P pDistinct) (hBi : BitsSpec lim P pBits) {a : Map} {V x : ℕ}
    {X : List ℤ} (C : Prep.Ctx lim d a V x X) {μ : ℕ → ℤ} (hseg : Seg μ x X) :
    Ends lim P d (prepBody pPrimes pFill pCopy pSort pDistinct pBits)
      ⟨frame [a.n, V, a.Λ, a.m, x, a.b], μ⟩ (tPrep a.n a.Λ a.m) fun σ' =>
      (∃ D M : List ℤ, σ'.loc 0 = (D.length : ℤ) ∧ Values a.n X D M ∧ Seg σ'.mem a.mul M ∧
        σ'.mem a.one = 0 ∧ FrontMem σ'.mem (a.front V D)) ∧ Kept μ σ'.mem a.b := by
  have hmap := a.layout
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hword := C.ok.word
  (((obtain ⟨⟩ := _root_.id C))
              )
  simp only [prepNeed] at hcells hword
  push_cast at hword
  have : (0 : ℤ) ≤ ((a.m : ℤ) + 1) ^ 2 := by positivity
  unfold tPrep prepBody
  refine Ends.next _ (Ends.block ((prepAddr_runs a V x μ (by omega) (by omega)).mono ?_) le_rfl)
    (by simp [prepAddr])
  rintro _ rfl
  refine Ends.next _ ((prepTables_ends hPr hFi a C.ok).mono le_rfl ?_) (by simp [prepAddr]; omega)
  rintro _ ⟨μ₁, r₁, rfl, hprimes, hzero, hkept₁⟩
  refine Ends.next _ ((prepSorted_ends hCo hSo C
    (hseg.of_sameOn hkept₁ fun i hi => ⟨by omega, by omega⟩) _ r₁).mono le_rfl ?_)
    (by simp [prepAddr]; omega)
  rintro _ ⟨μ₂, r₂, Ls, rfl, hLs, hperm, hsorted, hkept₂⟩
  refine Ends.next _ ((prepValues_ends hDi hBi C hLs hperm hsorted _ r₂).mono le_rfl ?_)
    (by simp [prepAddr]; omega)
  rintro _ ⟨μ₃, r₃, D, M, rfl, hvals, hkept₃⟩
  refine (prepTail_ends a r₃ (by omega) hw (by omega)).mono (by simp [prepAddr]; omega) ?_
  rintro ⟨_, μ₄⟩ ⟨hres, hctx, hone, hkept₄⟩
  have hlate : SameOn (· < a.srt) μ₁ μ₃ := hkept₂.then hkept₃ fun c hc => ⟨hc, by omega⟩
  obtain ⟨hmul, hfront⟩ := hvals.frontMem hprimes hzero hlate hctx hkept₄
  exact ⟨⟨D, M, hres, hvals.values, hmul, hone, hfront⟩,
    (hkept₁.then hlate fun c hc => ⟨⟨by omega, by omega⟩, by omega⟩).then hkept₄
      fun c hc => ⟨hc, by omega, by omega⟩⟩
theorem prep_spec {p pPrimes pFill pCopy pSort pDistinct pBits : ℕ}
    (hP : P[p]? = some (prepBody pPrimes pFill pCopy pSort pDistinct pBits))
    (hPr : PrimesSpec lim P pPrimes) (hFi : P[pFill]? = some fillBody)
    (hCo : P[pCopy]? = some copyBody) (hSo : SortSpec lim P pSort)
    (hDi : DistinctSpec lim P pDistinct) (hBi : BitsSpec lim P pBits) : PrepSpec lim P p :=
  fun _ _ _ _ _ _ C hseg => Meets.of_body hP (prepBody_ends hPr hFi hCo hSo hDi hBi C hseg)
end Light.Sec3.ChanHe
end
end
theorem solution :
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.emodBody → Light.Sec3.ChanHe.EmodSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.clog2Body → Light.Sec3.ChanHe.Clog2Spec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.log2Body → Light.Sec3.ChanHe.Log2Spec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.sieveBody → Light.Sec3.ChanHe.PrimesSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pHalf pMerge pCopy : ℕ},
  Light.MergeSort.Procs P p pHalf pMerge pCopy → Light.Sec3.ChanHe.SortSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.distinctBody → Light.Sec3.ChanHe.DistinctSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.bitsBody → Light.Sec3.ChanHe.BitsSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pEmod : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.residBody pEmod) →
    Light.Sec3.ChanHe.EmodSpec lim P pEmod → Light.Sec3.ChanHe.ResidSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.tallyBody → Light.Sec3.ChanHe.TallySpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.collBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.CollSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.heavyBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.HeavySpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {pSearch pColl p : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.modulusBody pSearch pColl) →
    P[pSearch]? = some (Light.Sec3.ChanHe.searchBody pColl) →
      Light.Sec3.ChanHe.CollSpec lim P pColl → Light.Sec3.ChanHe.ModulusSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.nodeArrayBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.NodeArraySpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pLog2 pClog2 pSqrt : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.paramsBody pLog2 pClog2 pSqrt) →
    Light.Sec3.ChanHe.Log2Spec lim P pLog2 →
      Light.Sec3.ChanHe.Clog2Spec lim P pClog2 → P[pSqrt]? = some Light.sqrtBody → Light.Sec3.ChanHe.ParamsSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pPrimes pFill pCopy pSort pDistinct pBits : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.prepBody pPrimes pFill pCopy pSort pDistinct pBits) →
    Light.Sec3.ChanHe.PrimesSpec lim P pPrimes →
      P[pFill]? = some Light.fillBody →
        P[pCopy]? = some Light.copyBody →
          Light.Sec3.ChanHe.SortSpec lim P pSort →
            Light.Sec3.ChanHe.DistinctSpec lim P pDistinct →
              Light.Sec3.ChanHe.BitsSpec lim P pBits → Light.Sec3.ChanHe.PrepSpec lim P p) :=
  ⟨@Light.Sec3.ChanHe.emodSpec_of, @Light.Sec3.ChanHe.clog2Spec_of, @Light.Sec3.ChanHe.log2Spec_of, @Light.Sec3.ChanHe.primesSpec_of, @Light.Sec3.ChanHe.sortSpec_of, @Light.Sec3.ChanHe.distinct_spec, @Light.Sec3.ChanHe.bits_spec, @Light.Sec3.ChanHe.resid_spec, @Light.Sec3.ChanHe.tally_spec, @Light.Sec3.ChanHe.coll_spec, @Light.Sec3.ChanHe.heavy_spec, @Light.Sec3.ChanHe.modulusSpec_of, @Light.Sec3.ChanHe.nodeArray_spec, @Light.Sec3.ChanHe.params_spec, @Light.Sec3.ChanHe.prep_spec⟩
#print axioms solution
