-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:45:17.708905+00:00
-- url     : https://prove2.me/submissions/2594d708-a917-4ab0-a35d-4f6f82f8f457

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eval_mul_of_commute
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eval_mul_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_commute_coeff_X_add_C
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eq_zero_of_eval
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_qdet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
theorem _root_.solution (H : QdetTens) (M : GMod n) (c : ℂ) (pC : (Module.End ℂ (Fin n → M.V))[X])
    (hC : ∀ y : ℂ, pC.eval (algebraMap ℂ _ y) = (qdet M.E (y + c)).compLeft (Fin n)) :
    pC.eval (-om M - algebraMap ℂ _ c) = 0 := by
  obtain ⟨pT, hT⟩ := polF_qdet (tensE M) c
  have hR : pT * (X + C (algebraMap ℂ _ c + om M)) - pC * (X + C (algebraMap ℂ _ (c + 1) + om M)) = 0 :=
    eq_zero_of_eval _ fun y => by
      rw [eval_sub, eval_mul_alg, eval_mul_alg, hT, hC, sub_eq_zero]
      simp only [eval_add, eval_X, eval_C]
      have h := H n M (y + c)
      have e1 : algebraMap ℂ (Module.End ℂ (Fin n → M.V)) y + (algebraMap ℂ _ c + om M) =
          (y + c) • (1 : Module.End ℂ (Fin n → M.V)) + om M := by
        rw [← add_assoc, ← map_add, Algebra.algebraMap_eq_smul_one]
      have e2 : algebraMap ℂ (Module.End ℂ (Fin n → M.V)) y + (algebraMap ℂ _ (c + 1) + om M) =
          (y + c + 1) • (1 : Module.End ℂ (Fin n → M.V)) + om M := by
        rw [← add_assoc, ← map_add, Algebra.algebraMap_eq_smul_one, add_assoc]
      rw [e1, e2]
      exact h
  have hom : Commute (om M) (-om M - algebraMap ℂ _ c) :=
    ((Commute.refl _).neg_right).sub_right (Algebra.commutes c _).symm
  have hd : ∀ d : ℂ, Commute (algebraMap ℂ (Module.End ℂ (Fin n → M.V)) d + om M) (-om M - algebraMap ℂ _ c) :=
    fun d => Commute.add_left (show Commute _ _ from Algebra.commutes d _) hom
  have ht := congrArg (eval (-om M - algebraMap ℂ _ c)) hR
  rw [eval_sub, eval_mul_of_commute _ _ _ (commute_coeff_X_add_C _ _ (hd c)),
    eval_mul_of_commute _ _ _ (commute_coeff_X_add_C _ _ (hd (c + 1)))] at ht
  simp only [eval_add, eval_X, eval_C, eval_zero] at ht
  have a1 : -om M - algebraMap ℂ _ c + (algebraMap ℂ _ c + om M) = 0 := by abel
  have a2 : -om M - algebraMap ℂ _ c + (algebraMap ℂ _ (c + 1) + om M) = 1 := by
    rw [map_add, map_one]; abel
  rw [a1, a2] at ht
  simpa using ht.symm
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
