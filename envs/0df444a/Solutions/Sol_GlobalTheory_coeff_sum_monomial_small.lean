-- Prove2me | solution 1 for GlobalTheory.coeff_sum_monomial_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:52.685803+00:00
-- url     : https://prove2.me/submissions/d5afd94a-6489-4e7c-8544-916588910cd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc
import Theorems.Thm_GlobalTheory_coeff_sum_monomial_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hgt : ∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) (j : ℕ) (hj : l ^ M < j) :
    ‖(∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j‖ * ρ ^ j
      < ‖(l : ℂ_[l])‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  by_cases h : ∃ k, k ≤ E ∧ l ^ k = j
  · obtain ⟨k, hkE, rfl⟩ := h
    rw [coeff_sum_monomial_pow l E a k hkE]
    have hMk : M < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hj
    exact hgt k hMk hkE
  · have h0 : (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j = 0 := by
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_monomial, if_neg]
      intro hij
      exact h ⟨i, by have := Finset.mem_range.mp hi; omega, hij⟩
    rw [h0, norm_zero, zero_mul]
    exact hlpos
end GlobalTheory
