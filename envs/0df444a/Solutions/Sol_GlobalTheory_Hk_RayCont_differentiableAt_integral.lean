-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.differentiableAt_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:51.903568+00:00
-- url     : https://prove2.me/submissions/96cc752c-f3df-47e0-870b-175385c06402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_mellin_indicator_eq
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_indicator_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable {E : ℝ → ℂ} {C : ℝ}
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution (hE : Measurable E)
    (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ t in Set.Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1)) s := by
  have h : DifferentiableAt ℂ (mellin ((Set.Ioi (1 : ℝ)).indicator E)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 2)) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      have hc : Continuous fun x : ℝ => C * Real.sqrt x := by fun_prop
      exact hc.locallyIntegrable.mono (hE.indicator measurableSet_Ioi).aestronglyMeasurable
        (Eventually.of_forall (norm_indicator_le hC))
    · refine IsBigO.of_bound ‖C‖ (Eventually.of_forall fun t => ?_)
      refine (norm_indicator_le hC t).trans (le_of_eq ?_)
      rw [norm_mul, neg_neg, Real.sqrt_eq_rpow]
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      rw [Set.indicator_of_notMem (fun h => lt_asymm (Set.mem_Ioi.1 h) (Set.mem_Iio.1 ht))]
      simp
    · simp
  have := h.comp s differentiableAt_id.neg
  simp only [← mellin_indicator_eq]
  exact this
end GlobalTheory.Hk.RayCont
