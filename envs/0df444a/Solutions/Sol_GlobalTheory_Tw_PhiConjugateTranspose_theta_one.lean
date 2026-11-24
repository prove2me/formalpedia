-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.theta_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:28.82949+00:00
-- url     : https://prove2.me/submissions/9cd4972a-629b-4cd7-a6d9-c49a21307327

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_mul_transpose
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.PhiConjugateTranspose
variable {n : ℕ} {R : Type} [CommRing R]
variable [StarRing R]
namespace GlobalTheory.Tw.PhiConjugateTranspose
theorem _root_.solution : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [theta_eq, inv_one, conjTranspose_one, Matrix.mul_one, phi_mul_transpose]
end GlobalTheory.Tw.PhiConjugateTranspose
