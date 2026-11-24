-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.phi_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:24.925651+00:00
-- url     : https://prove2.me/submissions/18825ac8-a40d-4954-8241-f80c72104388

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_transpose_mul

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
namespace GlobalTheory.Tw.PhiConjugateTranspose
theorem _root_.solution : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_left_inv phi_transpose_mul
end GlobalTheory.Tw.PhiConjugateTranspose
