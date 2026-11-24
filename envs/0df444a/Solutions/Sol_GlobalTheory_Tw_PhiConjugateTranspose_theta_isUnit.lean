-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.theta_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:17.378736+00:00
-- url     : https://prove2.me/submissions/7c780928-62be-461d-8fb0-eaabd21eecfc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_det_theta

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
theorem _root_.solution {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : IsUnit (theta g) := by
  rw [isUnit_iff_isUnit_det, det_theta]
  exact (isUnit_nonsing_inv_det _ ((isUnit_iff_isUnit_det g).mp hg)).star
end GlobalTheory.Tw.PhiConjugateTranspose
