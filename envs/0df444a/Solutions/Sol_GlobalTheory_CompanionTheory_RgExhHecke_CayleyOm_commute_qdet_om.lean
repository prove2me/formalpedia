-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.commute_qdet_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:05.736337+00:00
-- url     : https://prove2.me/submissions/da6ce520-44bc-4ffa-856c-27743c259c26

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
import Theorems.Thm_Formalism_REAL_qDetCentral


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
theorem _root_.solution (M : GMod n) (u : ℂ) : Commute ((qdet M.E u).compLeft (Fin n)) (om M) := by
  refine LinearMap.ext fun f => funext fun b => ?_
  have hc : ∀ (a : Fin n) (x : M.V), qdet M.E u (M.E a b x) = M.E a b (qdet M.E u x) := fun a x =>
    LinearMap.congr_fun (qDetCentral _ n M.E M.gl u a b) x
  show (qdet M.E u) (om M f b) = ∑ a, M.E a b (qdet M.E u (f a))
  rw [om_apply, map_sum]
  simp only [hc]
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
