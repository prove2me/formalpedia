-- Prove2me | solution 1 for GlobalTheory.Tw.Model.nrm_twConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:24.793095+00:00
-- url     : https://prove2.me/submissions/f9850941-b126-423a-bf51-0d1a4b0bea73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_GlobalTheory_Tw_Model_theta_mul
import Theorems.Thm_GlobalTheory_Tw_Model_theta_mul_theta_inv
import Theorems.Thm_GlobalTheory_Tw_Model_theta_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution {x δ : Matrix (Fin n) (Fin n) R} (hx : IsUnit x) :
    nrm (twConj x δ) = x⁻¹ * nrm δ * x := by
  have hx' : IsUnit x⁻¹ := by rwa [Matrix.isUnit_nonsing_inv_iff]
  simp only [nrm, twConj, theta_mul, theta_theta hx, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (theta x), theta_mul_theta_inv hx, Matrix.one_mul]
end GlobalTheory.Tw.Model
