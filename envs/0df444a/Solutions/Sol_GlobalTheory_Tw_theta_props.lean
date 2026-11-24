-- Prove2me | solution 1 for GlobalTheory.Tw.theta_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:15.07108+00:00
-- url     : https://prove2.me/submissions/145aefda-a388-46ee-9e12-ac28ceb94ac2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_mul_transpose
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_mul
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_one
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_det_theta
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_isUnit
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_theta
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_blockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory.Tw.PhiConjugateTranspose
namespace GlobalTheory.Tw
theorem _root_.solution : ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R], (Phi n R * (Phi n R)ᵀ = 1) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit (theta g) ∧ theta (theta g) = g) ∧ (∀ g h : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit h → theta (g * h) = theta g * theta h) ∧ (∀ x δ : Matrix (Fin n) (Fin n) R, IsUnit x → IsUnit δ → nrm (twConj x δ) = x⁻¹ * nrm δ * x) ∧ (∀ u δ : Matrix (Fin n) (Fin n) R, IsUnit u → IsUnit δ → nrm (δ * theta u) = nrm δ * ((theta δ)⁻¹ * theta u * theta δ) * u) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → g.BlockTriangular id → (theta g).BlockTriangular id) ∧ ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → (theta g).det * star g.det = 1 := by
  intro n R _ _
  refine ⟨phi_mul_transpose, fun g hg => ⟨theta_isUnit hg, theta_theta hg⟩, fun g h _ _ => theta_mul g h, ?_, ?_,
    fun g hg ht => theta_blockTriangular hg ht, ?_⟩
  · intro x δ hx _
    have hxd := (isUnit_iff_isUnit_det x).mp hx
    simp only [nrm, twConj, theta_mul, theta_theta hx]
    have h1 : theta x * theta x⁻¹ = 1 := by rw [← theta_mul, mul_nonsing_inv _ hxd, theta_one]
    calc x⁻¹ * δ * theta x * (theta x⁻¹ * theta δ * x)
        = x⁻¹ * δ * (theta x * theta x⁻¹) * theta δ * x := by simp only [Matrix.mul_assoc]
      _ = x⁻¹ * (δ * theta δ) * x := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  · intro u δ hu hδ
    have htd := (isUnit_iff_isUnit_det _).mp (theta_isUnit hδ)
    simp only [nrm, theta_mul, theta_theta hu]
    calc δ * theta u * (theta δ * u)
        = δ * (theta δ * (theta δ)⁻¹) * theta u * theta δ * u := by
          rw [mul_nonsing_inv _ htd, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = δ * theta δ * ((theta δ)⁻¹ * theta u * theta δ) * u := by simp only [Matrix.mul_assoc]
  · intro g hg
    have hd := (isUnit_iff_isUnit_det g).mp hg
    rw [det_theta, ← star_mul, ← det_mul, mul_nonsing_inv _ hd, det_one, star_one]
end GlobalTheory.Tw
