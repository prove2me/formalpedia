-- Prove2me | solution 1 for OAI.Problem310Support.positive_scale_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:11:16.334896+00:00
-- url     : https://prove2.me/submissions/3eb56203-87bc-499f-a27f-f052488e78e7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean:L36-L51
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.positive_scale_normalization. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GlobalFromPeriodic ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Every positive scale can be moved into `[1,2]` by a natural power
of two followed by passage to a dyadic tail. -/
theorem positive_scale_normalization {s : ℝ} (hs : 0 < s) :
    ∃ j m : ℕ, (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / s) (by norm_num : (1 : ℝ) < 2)
  have hlarge : 1 ≤ s * (2 : ℝ) ^ j := by
    have := (div_lt_iff₀ hs).mp hj
    nlinarith
  obtain ⟨m, hm₀, hm₁⟩ := exists_nat_pow_near hlarge (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, m, ?_, ?_⟩
  · rw [inv_pow]
    exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr (by simpa using hm₀)
  · rw [inv_pow]
    apply (mul_inv_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr
    rw [pow_succ] at hm₁
    nlinarith

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.positive_scale_normalization := @_root_.OAI.Problem310Support.positive_scale_normalization
