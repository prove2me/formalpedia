-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.conj_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:08.071992+00:00
-- url     : https://prove2.me/submissions/0c9982ad-0878-4bda-abc6-ce703b5a58a9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_inv
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_transpose_inv

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)⁻¹ = Phi n R * A⁻¹ * (Phi n R)ᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, phi_inv, phi_transpose_inv, Matrix.mul_assoc]
end GlobalTheory.Tw.PhiConjugateTranspose
