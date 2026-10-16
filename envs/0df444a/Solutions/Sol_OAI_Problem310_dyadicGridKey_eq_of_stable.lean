-- Prove2me | solution 1 for OAI.Problem310.dyadicGridKey_eq_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:19:33.528994+00:00
-- url     : https://prove2.me/submissions/0942ddc8-0766-44fe-bd9e-22396148020e

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridGeometry.lean:L176-L195
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.dyadicGridKey_eq_of_stable. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_periodicGridKey_eq_of_no_crossing

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridGeometry ----
namespace OAI

noncomputable section
namespace Problem310

private theorem half_pow_antitone : Antitone (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) :=
  pow_right_anti₀ (by norm_num) (by norm_num)

/-- The no-crossing stability condition for a later window preserves an earlier key. -/
theorem dyadicGridKey_eq_of_stable {a b n : ℕ} {x t : ℝ}
    (han : a ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hstable : ∀ k : ℤ, (k : ℝ) / (2 : ℝ) ^ (b + 2) ∉
      Set.Ioc x (x + 2 * ((2 : ℝ)⁻¹) ^ a)) :
    dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey b x := by
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
  have hp' : 0 ≤ ((2 : ℝ)⁻¹) ^ a := by positivity
  have hn := half_pow_antitone han
  have hstep : 0 ≤ t * ((2 : ℝ)⁻¹) ^ n :=
    mul_nonneg (by linarith [ht.1]) hp
  have hbound : t * ((2 : ℝ)⁻¹) ^ n ≤ 2 * ((2 : ℝ)⁻¹) ^ a := by
    nlinarith [ht.2]
  have hkey := periodicGridKey_eq_of_no_crossing ((2 : ℕ) ^ (b + 2))
    (by positivity) (show x ≤ x + t * ((2 : ℝ)⁻¹) ^ n by linarith)
    (fun k hk ↦ hstable k ⟨by simpa using hk.1, by
      have hk' : (k : ℝ) / (2 : ℝ) ^ (b + 2) ≤ x + t * ((2 : ℝ)⁻¹) ^ n := by
        simpa using hk.2
      linarith⟩)
  simpa [dyadicGridKey] using hkey.symm

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310


theorem solution : type_of% @_root_.OAI.Problem310.dyadicGridKey_eq_of_stable := @_root_.OAI.Problem310.dyadicGridKey_eq_of_stable
