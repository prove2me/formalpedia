-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.conj_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:07.205169+00:00
-- url     : https://prove2.me/submissions/5fd8001a-d13a-466e-91b9-6b59f34caeeb

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_conjTranspose
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_transpose_conjTranspose

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)ᴴ = Phi n R * Aᴴ * (Phi n R)ᵀ := by
  rw [conjTranspose_mul, conjTranspose_mul, phi_conjTranspose, phi_transpose_conjTranspose, Matrix.mul_assoc]
end GlobalTheory.Tw.PhiConjugateTranspose
