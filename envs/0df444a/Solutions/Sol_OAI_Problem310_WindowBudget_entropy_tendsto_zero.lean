-- Prove2me | solution 1 for OAI.Problem310.WindowBudget.entropy_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:55:02.410841+00:00
-- url     : https://prove2.me/submissions/36150a29-50f5-43ad-a86b-5c9b91418ad5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowBudgets.lean:L19-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowBudget.entropy_tendsto_zero. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowBudgets ----
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem310.WindowBudget

/-- A polynomial factor times a decaying exponential tends to zero along natural arguments. -/
lemma tendsto_nat_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℕ => (r : ℝ) * Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The entropy factor appearing in the finite scale discretization is dominated by
its exponential saving. This uses exactly the numerical coefficient. -/
lemma entropy_tendsto_zero (M a : ℝ) (ha : 10 ≤ a) :
    Tendsto (fun r : ℕ => 20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
      Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < a - 2 * Real.log 2 := by linarith
  have h1 := (tendsto_nat_mul_exp_neg a ha0).const_mul (20 * M)
  have h2 := (tendsto_nat_mul_exp_neg (a - 2 * Real.log 2) hb0).const_mul (80 * M)
  have hsum := h1.add h2
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with r
  have hpow : (2 : ℝ) ^ (2 * r + 2) =
      Real.exp (((2 * r + 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hfour : Real.exp (2 * Real.log 2) = 4 := by
    convert Real.exp_nat_mul (Real.log 2) 2 using 1 <;> norm_num [Real.exp_log]
  have hprod : (2 : ℝ) ^ (2 * r + 2) * Real.exp (-a * (r : ℝ)) =
      4 * Real.exp (-(a - 2 * Real.log 2) * (r : ℝ)) := by
    rw [hpow, ← Real.exp_add, ← hfour, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    20 * M * ((r : ℝ) * Real.exp (-a * (r : ℝ))) +
        80 * M * ((r : ℝ) * Real.exp (-(a - 2 * Real.log 2) * (r : ℝ))) =
        20 * M * (r : ℝ) * Real.exp (-a * (r : ℝ)) +
        20 * M * (r : ℝ) * ((2 : ℝ) ^ (2 * r + 2) * Real.exp (-a * (r : ℝ))) := by
          rw [hprod]
          ring
    _ = _ := by ring

end Problem310.WindowBudget

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowBudget
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Problem310.WindowBudget.entropy_tendsto_zero := @_root_.OAI.Problem310.WindowBudget.entropy_tendsto_zero
