-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgHeckeBack.tensVd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:31.65983+00:00
-- url     : https://prove2.me/submissions/6f1a1032-db84-4fca-8852-6c1c5e8722cf

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgHeckeBack
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgHeckeBack
theorem _root_.solution (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]
end GlobalTheory.CompanionTheory.RgHeckeBack
