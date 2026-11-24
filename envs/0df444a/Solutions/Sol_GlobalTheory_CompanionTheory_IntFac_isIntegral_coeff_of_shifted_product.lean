-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:26.492803+00:00
-- url     : https://prove2.me/submissions/ab918641-3331-484e-9815-4616d661055b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_coeff_of_eval
import Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_eval_of_coeff
import Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_coeff_of_monic_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.CompanionTheory.IntFac
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic →
      (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) *
        Q.eval (algebraMap ℂ A (u + c₂)))) →
      ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  intro A _ _ P Q c₁ c₂ hP hQ h k
  set P₁ := P.comp (X + C (algebraMap ℂ A c₁)) with hP₁d
  set Q₁ := Q.comp (X + C (algebraMap ℂ A c₂)) with hQ₁d
  have hP₁ : P₁.Monic := hP.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQ.comp_X_add_C _
  have hH : ∀ j, IsIntegral ℂ ((P₁ * Q₁).coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A (P₁ * Q₁)
      (fun u => by simpa [hP₁d, hQ₁d, eval_comp] using h u)
  have i₁ : ∀ j, IsIntegral ℂ (P₁.coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hP₁ (dvd_mul_right _ _) hH
  have i₂ : ∀ j, IsIntegral ℂ (Q₁.coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hQ₁ (dvd_mul_left _ _) hH
  refine ⟨GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A P (fun u => ?_) k,
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A Q (fun u => ?_) k⟩
  · have h₁ := GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A P₁ i₁ (u - c₁)
    simpa [hP₁d, eval_comp] using h₁
  · have h₂ := GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A Q₁ i₂ (u - c₂)
    simpa [hQ₁d, eval_comp] using h₂
end GlobalTheory.CompanionTheory.IntFac
