-- Prove2me | solution 1 for OAI.Problem310.SelectorMoment.lookup_fair_failure_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:34:39.096983+00:00
-- url     : https://prove2.me/submissions/808a518d-2973-449d-8880-4ba996a50ce6

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/SelectorMoment.lean:L77-L100
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.SelectorMoment.lookup_fair_failure_moment. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_SelectorMoment_independent_boolean_moment

-- ---- from OAI.MeasureTheory.DyadicAvoidance.SelectorMoment ----
namespace OAI

universe u_I u_Ω u_K

noncomputable section

namespace Problem310.SelectorMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The same moment for injective coordinate lookups in a larger product table. -/
theorem lookup_boolean_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr) (q : ℝ≥0∞) :
    (∫⁻ ω : K → Bool, q ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by
  apply independent_boolean_moment
  · exact iIndepFun.precomp hinj
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id))
  · intro i
    exact measurable_pi_apply (addr i)
  · intro i
    exact (measurePreserving_eval (fun _ : K => ν) (addr i)).map_eq

/-- Fair fresh selector entries, with an arbitrary nonnegative failure factor. -/
theorem lookup_fair_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr) (q : ℝ≥0∞) :
    (∫⁻ ω : K → Bool, q ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (1 / 2 + q / 2) ^ Fintype.card I := by
  rw [lookup_boolean_moment ν addr hinj q, hfalse, htrue]
  simp [div_eq_mul_inv]

/-- The exact fixed-scale base, with real parameter p. -/
theorem lookup_fair_failure_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr)
    (p : ℝ) (hp : p ≤ 1) :
    (∫⁻ ω : K → Bool, (ENNReal.ofReal (1 - p)) ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  rw [lookup_fair_moment ν hfalse htrue addr hinj]
  congr 1
  have hdiv (a : ℝ) : ENNReal.ofReal (a / 2) = ENNReal.ofReal a / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [hdiv]
    norm_num
  rw [hhalf, ← hdiv]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (div_nonneg (sub_nonneg.mpr hp) (by norm_num))]
  congr 1
  ring

end Problem310.SelectorMoment

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.SelectorMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal


theorem solution.{u_I,u_K} : type_of% @_root_.OAI.Problem310.SelectorMoment.lookup_fair_failure_moment.{u_I,u_K} := @_root_.OAI.Problem310.SelectorMoment.lookup_fair_failure_moment.{u_I,u_K}
