-- Prove2me | solution 1 for OAI.Problem310Support.signedDyadicUnion_hits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:13:17.930419+00:00
-- url     : https://prove2.me/submissions/b152c44e-af8d-4d40-8f94-a627fc1865a5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean:L76-L103
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.signedDyadicUnion_hits. The node keeps its source
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
import Theorems.Thm_OAI_Problem310Support_positive_scale_normalization

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GlobalFromPeriodic ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

theorem signedDyadicUnion_neg {H : ℕ → Set ℝ} {x : ℝ}
    (hx : x ∈ signedDyadicUnion H) : -x ∈ signedDyadicUnion H := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  rcases hj with hj | hj
  · right
    simpa only [mem_ofPred_eq, mul_neg, neg_neg] using hj
  · left
    simpa only [mem_ofPred_eq, mul_neg] using hj

/-- The full signed-scale hitting property is a purely algebraic consequence
of a normalized hitting set at every dyadic magnification. -/
theorem signedDyadicUnion_hits {H : ℕ → Set ℝ}
    (hH : ∀ j (x t : ℝ), t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H j) :
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by
  have hpos : ∀ x s : ℝ, 0 < s → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by
    intro x s hs
    obtain ⟨j, m, hscale⟩ := positive_scale_normalization hs
    obtain ⟨n, hn, hhit⟩ := hH j ((2 : ℝ) ^ j * x)
      (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) hscale
    refine ⟨m + n, by omega, mem_iUnion.mpr ⟨j, Or.inl ?_⟩⟩
    change (2 : ℝ) ^ j * (x + s * ((2 : ℝ)⁻¹ ^ (m + n))) ∈ H j
    have heq : (2 : ℝ) ^ j * (x + s * ((2 : ℝ)⁻¹ ^ (m + n))) =
        (2 : ℝ) ^ j * x +
          (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) * ((2 : ℝ)⁻¹ ^ n) := by
      rw [pow_add]
      ring
    rwa [heq]
  intro x s hs
  rcases lt_or_gt_of_ne hs with hs | hs
  · obtain ⟨n, hn, hhit⟩ := hpos (-x) (-s) (neg_pos.mpr hs)
    refine ⟨n, hn, ?_⟩
    have := signedDyadicUnion_neg hhit
    simpa only [neg_add, neg_neg, neg_mul] using this
  · exact hpos x s hs

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.signedDyadicUnion_hits := @_root_.OAI.Problem310Support.signedDyadicUnion_hits
