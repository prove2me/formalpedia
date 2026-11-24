-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.det_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:37.41284+00:00
-- url     : https://prove2.me/submissions/13ed0f76-e7e0-45bb-9069-29813b29be80

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_det_conj
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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) : (theta g).det = star (g⁻¹).det := by
  rw [theta_eq, det_conj, det_conjTranspose]
end GlobalTheory.Tw.PhiConjugateTranspose
