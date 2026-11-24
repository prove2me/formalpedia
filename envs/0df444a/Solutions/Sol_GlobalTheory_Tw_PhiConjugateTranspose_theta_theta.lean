-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.theta_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:33.569997+00:00
-- url     : https://prove2.me/submissions/c8991962-668e-4a5c-a097-b27be5dcb632

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_mul_phi
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_conj_inv
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_conj_conjTranspose
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
theorem _root_.solution {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  have hd := (isUnit_iff_isUnit_det g).mp hg
  rw [theta_eq (theta g), theta_eq g, conj_inv, conj_conjTranspose, ← conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ hd, conjTranspose_conjTranspose]
  have h2 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← transpose_mul, phi_mul_phi, transpose_smul, transpose_one]
  calc Phi n R * (Phi n R * g * (Phi n R)ᵀ) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by
      rw [phi_mul_phi, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← mul_pow]
      simp
end GlobalTheory.Tw.PhiConjugateTranspose
