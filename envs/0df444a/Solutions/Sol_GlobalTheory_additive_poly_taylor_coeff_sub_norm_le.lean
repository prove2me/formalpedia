-- Prove2me | solution 1 for GlobalTheory.additive_poly_taylor_coeff_sub_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:14.591571+00:00
-- url     : https://prove2.me/submissions/964b4082-5ffc-4b86-a899-2d7744f3c478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro l hl E a W ha hW j hj
  have hp : l.Prime := hl.out
  rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  have hak : ‖a k‖ ≤ 1 := ha k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Polynomial.taylor_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow]
  rcases lt_trichotomy j (l ^ k) with h | h | h
  · have hne : j ≠ l ^ k := h.ne
    simp only [hne, if_false, mul_zero, sub_zero]
    obtain ⟨m, hm⟩ : l ∣ (l ^ k).choose j := hp.dvd_choose_pow (by omega) h.ne
    rw [hm, Nat.cast_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖W ^ (l ^ k - j)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hW
    have h2 : ‖(m : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
    calc ‖a k‖ * (‖W ^ (l ^ k - j)‖ * (‖(l : ℂ_[l])‖ * ‖(m : ℂ_[l])‖))
        ≤ 1 * (1 * (‖(l : ℂ_[l])‖ * 1)) := by gcongr
      _ = ‖(l : ℂ_[l])‖ := by ring
  · subst h
    simp
  · have hne : j ≠ l ^ k := h.ne'
    simp only [hne, if_false, mul_zero, sub_zero, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
    simp
end GlobalTheory
