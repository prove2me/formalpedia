-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgHeckeBack.commute_tensVd_eeVd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:05.374299+00:00
-- url     : https://prove2.me/submissions/81573b83-86e0-41e8-9639-8f4d59defb06

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStable
import Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_tensVd_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_eeVd_apply

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
theorem _root_.solution (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_
  simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]
end GlobalTheory.CompanionTheory.RgHeckeBack
