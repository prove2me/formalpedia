-- Prove2me | solution 1 for OAI.Problem310Support.periodic_reflect_unit_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:06:24.775219+00:00
-- url     : https://prove2.me/submissions/60c747ed-b9f6-42bc-8b66-7a9b48e9e2a2

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean:L92-L109
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.periodic_reflect_unit_volume. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Reflection preserves the occupied volume in a unit period. -/
theorem periodic_reflect_unit_volume {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    volume ({x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1) =
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hset : {x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1 =
      (fun x : ℝ => -x) ⁻¹' ((fun y : ℝ => 1 + y) ⁻¹'
        (H ∩ Icc (0 : ℝ) 1)) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    have hmem : 1 + -x ∈ H ↔ -x ∈ H := by simpa only [add_comm] using hH (-x)
    rw [hmem]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
  rw [hset, Measure.measure_preimage_neg, measure_preimage_add]

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.periodic_reflect_unit_volume := @_root_.OAI.Problem310Support.periodic_reflect_unit_volume
