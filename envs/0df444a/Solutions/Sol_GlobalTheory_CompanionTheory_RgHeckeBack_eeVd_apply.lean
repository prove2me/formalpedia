-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgHeckeBack.eeVd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:20.692957+00:00
-- url     : https://prove2.me/submissions/c8427f47-ce76-4c42-bda0-b7831c945653

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
theorem _root_.solution (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]
end GlobalTheory.CompanionTheory.RgHeckeBack
