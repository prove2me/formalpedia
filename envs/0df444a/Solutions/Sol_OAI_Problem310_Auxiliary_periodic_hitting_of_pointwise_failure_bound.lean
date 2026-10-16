-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.periodic_hitting_of_pointwise_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:48:15.995106+00:00
-- url     : https://prove2.me/submissions/5cec698f-2cb6-4dd4-af5b-92df332c47f7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExpectedRepair.lean:L47-L79
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.periodic_hitting_of_pointwise_failure_bound. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_Auxiliary_expected_density_le_of_pointwise_bound
import Theorems.Thm_OAI_Problem310_Auxiliary_isClosed_exceptionalCenters
import Theorems.Thm_OAI_Problem310_Auxiliary_periodic_hitting_of_expected_exceptional

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExpectedRepair ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set Filter Topology MeasureTheory

/-- Full analytic repair interface from pointwise failure probabilities on stable centers. -/
theorem periodic_hitting_of_pointwise_failure_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBo : ∀ ω, IsOpen (B ω))
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal (2 * p))
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  apply periodic_hitting_of_expected_exceptional μ p hp B hBo hBp N hN hBmean
  have hRm : ∀ ω, MeasurableSet
      (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)) :=
    fun ω => (isClosed_exceptionalCenters (B ω) (hBo ω) N _).measurableSet
  calc
    (∫⁻ ω, volume
        (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1) ∂μ)
        ≤ ENNReal.ofReal (2 * p) + volume (Gᶜ ∩ Icc (0 : ℝ) 1) :=
      expected_density_le_of_pointwise_bound μ _ hRm G hG _ hgood
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal p := add_le_add le_rfl hbad
    _ = ENNReal.ofReal (3 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hp)]
      congr 1
      ring

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology MeasureTheory


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.Auxiliary.periodic_hitting_of_pointwise_failure_bound.{u_Ω} := @_root_.OAI.Problem310.Auxiliary.periodic_hitting_of_pointwise_failure_bound.{u_Ω}
