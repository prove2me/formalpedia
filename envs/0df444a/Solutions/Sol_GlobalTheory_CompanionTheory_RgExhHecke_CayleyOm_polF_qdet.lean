-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.polF_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:30:13.461772+00:00
-- url     : https://prove2.me/submissions/c4dde799-e330-4209-b110-9ecf7753e9de

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_const
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_ofFn
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_Tm

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
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (c : ℂ) : PolF fun y : ℂ => qdet E (y + c) := by
  unfold qdet qminor
  refine polF_sum _ _ fun σ => (polF_const _).mul ?_
  have h := polF_ofFn (fun k : Fin n => fun y : ℂ => Tm E (y + (c - (k : ℂ))) (id (σ k)) (id k))
    fun k => polF_Tm E _ _ _
  simpa only [add_sub_assoc] using h
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
