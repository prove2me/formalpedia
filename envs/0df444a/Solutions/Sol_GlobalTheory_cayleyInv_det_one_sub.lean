-- Prove2me | solution 1 for GlobalTheory.cayleyInv_det_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:02.185464+00:00
-- url     : https://prove2.me/submissions/bba5fc38-9f3b-402c-bc20-242b6e9ca222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily
import Theorems.Thm_GlobalTheory_cayleyInv_one_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
variable {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    IsUnit (1 - (X - 1) * (X + 1)⁻¹).det := by
  rw [cayleyInv_one_sub _ hu, isUnit_iff_ne_zero]
  intro h0
  have h2 : ((2:ℂ) • (X + 1)⁻¹ * (X + 1)).det = (2:ℂ) ^ n := by
    rw [smul_mul_assoc, nonsing_inv_mul _ hu, det_smul, det_one, mul_one, Fintype.card_fin]
  rw [det_mul, h0, zero_mul] at h2
  exact (pow_ne_zero n two_ne_zero) h2.symm
end GlobalTheory
