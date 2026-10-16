-- Prove2me | solution 1 for OAI.Problem310.exists_dyadic_gap_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:26:40.801386+00:00
-- url     : https://prove2.me/submissions/8c1db16a-2472-4298-9b0e-905f327a8a56

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridStability.lean:L120-L135
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.exists_dyadic_gap_budget. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridStability ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Any prescribed finite number of stability conditions has arbitrarily small
exceptional density once the unused gap is sufficiently long. -/
theorem exists_dyadic_gap_budget (K : ℕ) {p : ℝ} (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ (K : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) < p := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < p / (4 * (K + 1 : ℝ)) by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨n + 2, by omega, ?_⟩
  have hpow := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) (show n ≤ n + 2 by omega)
  change (2 : ℝ)⁻¹ ^ (n + 2) ≤ (2 : ℝ)⁻¹ ^ n at hpow
  have hden : 0 < 4 * (K + 1 : ℝ) := by positivity
  have hlt := (lt_div_iff₀ hden).mp hn
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hnonneg : 0 ≤ ((2 : ℝ)⁻¹) ^ (n + 2) := by positivity
  nlinarith

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310
open MeasureTheory Set


theorem solution : type_of% @_root_.OAI.Problem310.exists_dyadic_gap_budget := @_root_.OAI.Problem310.exists_dyadic_gap_budget
