-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.expected_density_eq_pointwise_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:57:47.132361+00:00
-- url     : https://prove2.me/submissions/9b322eb0-135c-4887-a27d-c8f017302d25

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalExpectation.lean:L13-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.expected_density_eq_pointwise_probability. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalExpectation ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- For a finite random family of measurable sets, averaging their densities is
identical to integrating pointwise membership probabilities. -/
theorem expected_density_eq_pointwise_probability
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω)) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) =
      ∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω} := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let S : Set (Ω × ℝ) := {z | z.2 ∈ R z.1}
  have hS : MeasurableSet S := by
    have heq : S = ⋃ ω, ({ω} : Set Ω) ×ˢ R ω := by
      ext ⟨ω, x⟩
      simp [S]
    rw [heq]
    exact MeasurableSet.iUnion fun ω => (measurableSet_singleton ω).prod (hR ω)
  have heq := (Measure.prod_apply (μ := μ) (ν := ν) hS).symm.trans
    (Measure.prod_apply_symm (μ := μ) (ν := ν) hS)
  change (∫⁻ ω, ν (R ω) ∂μ) = ∫⁻ x, μ {ω | x ∈ R ω} ∂ν at heq
  simpa only [ν, Measure.restrict_apply (hR _)] using heq

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set MeasureTheory


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.Auxiliary.expected_density_eq_pointwise_probability.{u_Ω} := @_root_.OAI.Problem310.Auxiliary.expected_density_eq_pointwise_probability.{u_Ω}
