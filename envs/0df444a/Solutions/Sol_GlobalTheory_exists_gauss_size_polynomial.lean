-- Prove2me | solution 1 for GlobalTheory.exists_gauss_size_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:39.593658+00:00
-- url     : https://prove2.me/submissions/d1379ecd-8f71-4f3b-b4cf-8c0c80794150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsogenyNumeratorCoeffNormLeOne

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
theorem _root_.solution (K : Type) [NormedField K] [IsUltrametricDist K] :
    ∃ G : K[X] → ℝ, (∀ p, 0 ≤ G p) ∧ (∀ p i, ‖p.coeff i‖ ≤ G p) ∧
      (∀ p r, (∀ i, ‖p.coeff i‖ ≤ r) → G p ≤ r) ∧
      (∀ p q, G (p * q) = G p * G q) ∧ (∀ p q, G (p + q) ≤ max (G p) (G q)) ∧
      (∀ a, G (C a) = ‖a‖) ∧ G X = 1 := by
  let v : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have hv : ∀ a, v a = ‖a‖ := fun _ => rfl
  have hna : IsNonarchimedean v := fun a b => IsUltrametricDist.norm_add_le_max a b
  refine ⟨gaussNorm v 1, fun p => gaussNorm_nonneg v p zero_le_one, fun p i => ?_,
    fun p r hr => ?_, fun p q => gaussNorm_mul hna one_pos p q,
    fun p q => isNonarchimedean_gaussNorm v hna zero_le_one p q, fun a => ?_, ?_⟩
  · simpa [hv] using le_gaussNorm v p zero_le_one i
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v 1 p
    rw [hi, hv, one_pow, mul_one]
    exact hr i
  · rw [gaussNorm_C, hv]
  · rw [← monomial_one_one_eq_X, gaussNorm_monomial, hv]
    simp
end GlobalTheory
