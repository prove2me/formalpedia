-- Prove2me | solution 1 for OAI.Problem310.gridBadCenters_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:21:25.930624+00:00
-- url     : https://prove2.me/submissions/cf88ad92-b4fb-4d25-bb54-838eab0fc284

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean:L31-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.gridBadCenters_add_one. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridMeasure ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

theorem mem_gridBadCenters_iff (q : ℕ) (δ x : ℝ) :
    x ∈ gridBadCenters q δ ↔ ∃ k : ℤ, (k : ℝ) / q ∈ Ioc x (x + δ) := by
  simp only [gridBadCenters, mem_iUnion, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.2], by linarith [hk.1]⟩

theorem gridBadCenters_add_one (q : ℕ) (hq : 0 < q) (δ x : ℝ) :
    x + 1 ∈ gridBadCenters q δ ↔ x ∈ gridBadCenters q δ := by
  rw [mem_gridBadCenters_iff, mem_gridBadCenters_iff]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - q, ?_⟩
    have he : ((k - q : ℤ) : ℝ) / q = (k : ℝ) / q - 1 := by
      push_cast
      field_simp
    rw [he]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k + q, ?_⟩
    have he : ((k + q : ℤ) : ℝ) / q = (k : ℝ) / q + 1 := by
      push_cast
      field_simp
    rw [he]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310
open MeasureTheory Set


theorem solution : type_of% @_root_.OAI.Problem310.gridBadCenters_add_one := @_root_.OAI.Problem310.gridBadCenters_add_one
