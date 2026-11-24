-- Prove2me | solution 1 for GlobalTheory.isUnit_det_of_dual_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:31.776312+00:00
-- url     : https://prove2.me/submissions/1807dc91-0c52-4e1e-8282-953e19b88225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ}
    (S A B C D A' C' : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det)
    (h1 : Aᵀ * (S * C') + Cᵀ * (S * A') = 0)
    (h2 : IsUnit (Bᵀ * (S * C') + Dᵀ * (S * A')).det) : IsUnit A'.det := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hSC : S * C' = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by
    have h1' : Aᵀ * (S * C') = -(Cᵀ * (S * A')) := eq_neg_of_add_eq_zero_left h1
    calc S * C' = Aᵀ⁻¹ * (Aᵀ * (S * C')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAt, Matrix.one_mul]
      _ = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by rw [h1', Matrix.mul_neg]
  have key : Bᵀ * (S * C') + Dᵀ * (S * A') = (Dᵀ - Bᵀ * Aᵀ⁻¹ * Cᵀ) * (S * A') := by
    rw [hSC]
    generalize Aᵀ⁻¹ = M
    noncomm_ring
  rw [key, Matrix.det_mul, Matrix.det_mul] at h2
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h2)
end GlobalTheory
