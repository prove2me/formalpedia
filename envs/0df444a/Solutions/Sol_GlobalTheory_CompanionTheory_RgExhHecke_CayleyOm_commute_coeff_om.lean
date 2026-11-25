-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.commute_coeff_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:18.60029+00:00
-- url     : https://prove2.me/submissions/f9a3047f-c707-4a88-8be1-7c75556de3a5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eval_mul_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_eq_zero_of_eval

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
theorem _root_.solution (M : GMod n) (p : (Module.End ℂ (Fin n → M.V))[X])
    (h : ∀ y : ℂ, Commute (p.eval (algebraMap ℂ _ y)) (om M)) (k : ℕ) : Commute (p.coeff k) (om M) := by
  have h0 : p * C (om M) - C (om M) * p = 0 := eq_zero_of_eval _ fun y => by
    rw [eval_sub, eval_mul_alg, eval_mul_alg, eval_C, sub_eq_zero]
    exact h y
  have hk := congrArg (fun r => r.coeff k) h0
  simp only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero, sub_eq_zero] at hk
  exact hk
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
