-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.geom_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:10.716259+00:00
-- url     : https://prove2.me/submissions/d4770d58-b6e4-46c7-b70c-5f785b15a828

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
namespace GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
private lemma sum_range_neg_one_pow_eq_ite (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', h.neg_one_pow]
      norm_num
    · have h' : Even (n + 1) := Nat.even_add_one.2 h
      rw [if_neg h, if_pos h', (Nat.not_even_iff_odd.1 h).neg_one_pow]
      norm_num
variable {M : ℕ} (D : RayData K M)
end GlobalTheory.Hk.RaySq
end
end

set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution {x : ℝ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), x ^ i ∧ 1 ≤ ∑ i ∈ Finset.range (2 * k + 1), x ^ i := by
  rcases hx with rfl | rfl | rfl
  · simp [Finset.sum_range_succ']
  · simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    refine ⟨by positivity, ?_⟩
    push_cast
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rw [sum_range_neg_one_pow_eq_ite, sum_range_neg_one_pow_eq_ite]
    have h : ¬ Even (2 * k + 1) := by
      rw [Nat.even_add_one, not_not]
      exact even_two_mul k
    rw [if_neg h]
    refine ⟨?_, le_refl _⟩
    split_ifs <;> norm_num
end GlobalTheory.Hk.RaySq
