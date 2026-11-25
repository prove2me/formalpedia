-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.evAt_qdetPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:01.222268+00:00
-- url     : https://prove2.me/submissions/fd840296-0a93-43fe-ac5d-19555df09db8

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_evAt_tmPoly

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evAt u (qdetPoly E) = qdet E u := by
  unfold qdet qminor qdetPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  simp [Function.comp_def, evAt_tmPoly]
end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
