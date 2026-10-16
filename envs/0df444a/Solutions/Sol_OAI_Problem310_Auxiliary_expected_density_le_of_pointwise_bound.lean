-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.expected_density_le_of_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:59:18.224647+00:00
-- url     : https://prove2.me/submissions/31b8f09c-2009-4260-b068-eb629f78bc66

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalExpectation.lean:L34-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.expected_density_le_of_pointwise_bound. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_Auxiliary_expected_density_eq_pointwise_probability

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalExpectation ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- A uniform bound outside a small exceptional set of centers controls the
expected density. This is the integration step in the repair argument. -/
theorem expected_density_le_of_pointwise_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω))
    (G : Set ℝ) (hG : MeasurableSet G) (a : ENNReal)
    (hgood : ∀ x ∈ G, μ {ω | x ∈ R ω} ≤ a) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤
      a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by
  rw [expected_density_eq_pointwise_probability μ R hR]
  calc
    (∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω}) ≤
        ∫⁻ x in Icc (0 : ℝ) 1, a + Gᶜ.indicator (fun _ => (1 : ENNReal)) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ G
      · simpa [hx] using hgood x hx
      · simp only [mem_compl_iff, hx, not_false_eq_true, indicator_of_mem]
        exact (prob_le_one).trans (le_add_self)
    _ = a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by
      rw [lintegral_add_left measurable_const]
      simp [lintegral_indicator hG.compl, Measure.restrict_apply hG.compl]

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set MeasureTheory


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.Auxiliary.expected_density_le_of_pointwise_bound.{u_Ω} := @_root_.OAI.Problem310.Auxiliary.expected_density_le_of_pointwise_bound.{u_Ω}
