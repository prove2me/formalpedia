-- Prove2me | solution 1 for OAI.Problem310.RandomSetDensity.pointwise_probability_selectedSet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:00:57.287206+00:00
-- url     : https://prove2.me/submissions/6c216d86-f696-43c0-808e-29a2728f1f6f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RandomSetDensity.lean:L32-L52
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RandomSetDensity.pointwise_probability_selectedSet. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RandomSetDensity ----
namespace OAI

universe u_A u_K

noncomputable section

open MeasureTheory

namespace Problem310.RandomSetDensity

/-- Independence of terminal labels from selectors gives the same membership
probability at every spatial point, even with adaptively selected addresses. -/
theorem pointwise_probability_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (x : ℝ) :
    (P.prod (Measure.pi (fun _ : K => ν))) {z | x ∈ selectedSet addr z} =
      ν {true} := by
  classical
  have hmeas : MeasurableSet {z : A × (K → Bool) | x ∈ selectedSet addr z} :=
    (Set.toFinite _).measurableSet
  rw [Measure.prod_apply hmeas]
  have hsection (a : A) :
      (Measure.pi (fun _ : K => ν)) {ω : K → Bool | ω (addr a x) = true} = ν {true} := by
    exact (measurePreserving_eval (fun _ : K => ν) (addr a x)).measure_preimage
      (measurableSet_singleton true).nullMeasurableSet
  change (∫⁻ a, (Measure.pi (fun _ : K => ν))
    {ω : K → Bool | ω (addr a x) = true} ∂P) = ν {true}
  simp only [hsection]
  simp

end Problem310.RandomSetDensity

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RandomSetDensity
open MeasureTheory


theorem solution.{u_A,u_K} : type_of% @_root_.OAI.Problem310.RandomSetDensity.pointwise_probability_selectedSet.{u_A,u_K} := @_root_.OAI.Problem310.RandomSetDensity.pointwise_probability_selectedSet.{u_A,u_K}
