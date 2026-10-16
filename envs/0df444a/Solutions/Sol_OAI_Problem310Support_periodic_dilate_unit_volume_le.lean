-- Prove2me | solution 1 for OAI.Problem310Support.periodic_dilate_unit_volume_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:04:35.463983+00:00
-- url     : https://prove2.me/submissions/83e3a43e-2002-4f7f-bf64-f0c4c143339d

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean:L60-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.periodic_dilate_unit_volume_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Theorems.Thm_OAI_Problem310Support_periodic_nat_interval_volume_le

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Pulling a period-one set back by a positive integer dilation cannot
increase the volume occupied inside the unit interval. -/
theorem periodic_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1 =
      (fun x : ℝ => (n : ℝ) * x) ⁻¹' (H ∩ Icc (0 : ℝ) (n : ℝ)) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, mul_nonneg hnR.le h₀, by nlinarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by nlinarith, by nlinarith⟩
  rw [hset, Real.volume_preimage_mul_left hnR.ne', abs_of_pos (inv_pos.mpr hnR)]
  have hbound := mul_le_mul_right (periodic_nat_interval_volume_le hH n)
    (ENNReal.ofReal ((n : ℝ)⁻¹))
  refine hbound.trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp), one_mul]

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.periodic_dilate_unit_volume_le := @_root_.OAI.Problem310Support.periodic_dilate_unit_volume_le
