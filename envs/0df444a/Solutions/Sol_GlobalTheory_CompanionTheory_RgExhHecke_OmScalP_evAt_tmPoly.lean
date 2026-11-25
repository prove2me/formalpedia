-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.evAt_tmPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:03.773733+00:00
-- url     : https://prove2.me/submissions/63808245-5b92-4c0d-957e-26d98492ea10

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_evAt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (v u : ℂ) (a b : Fin n) :
    evAt u (tmPoly E v a b) = Tm E (u - v) a b := by
  unfold tmPoly Tm
  by_cases h : a = b <;> simp [h, evAt_apply, map_sub]
end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
