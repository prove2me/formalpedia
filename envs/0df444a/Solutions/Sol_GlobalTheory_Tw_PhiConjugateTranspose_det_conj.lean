-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.det_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:23.254949+00:00
-- url     : https://prove2.me/submissions/685ac43c-3e0a-4cf0-ac75-aff44fb2195b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_mul_transpose

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) R) : (Phi n R * A * (Phi n R)ᵀ).det = A.det := by
  rw [det_mul, det_mul, mul_comm (Phi n R).det, mul_assoc, ← det_mul, phi_mul_transpose, det_one, mul_one]
end GlobalTheory.Tw.PhiConjugateTranspose
