-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_triplet_finite_jump_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:41:59.285054+00:00
-- url     : https://prove2.me/submissions/39d1fa3d-55d3-48c0-8856-9c76bae60437
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_negative_levy_cutoffs
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_compensated_real_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_triplet_transform_law
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Mathlib.Tactic.Choose

open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (T : LevyKhintchineTriple) (hneg : T.levyMeasure (Set.Ici (0 : ℝ)) = 0)
    (σ : ℝ) (hσ : σ ^ 2 = (T.gaussianVariance : ℝ)) (t : ℝ≥0) :
    ∃ μs : ℕ → ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop
        (nhds (Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ)))) ∧
      (∀ β : ℝ, 0 ≤ β →
        (∀ n, Integrable (fun x => Real.exp (β * x)) (μs n : Measure ℝ)) ∧
        Tendsto (fun n => ∫ x, Real.exp (β * x) ∂(μs n : Measure ℝ)) atTop
          (nhds (Real.exp ((t : ℝ) * tripletLaplace (-T.drift) σ T.levyMeasure β)))) := by
  classical
  let ν (n : ℕ) := T.levyMeasure.restrict (Iic (-(((n : ℝ) + 1)⁻¹)))
  obtain ⟨hfin, hlim⟩ := source_result81_negative_levy_cutoffs T.levyMeasure
    T.levyMeasure_isLevyMeasure hneg
  have hn (n : ℕ) : ν n (Ici (0 : ℝ)) = 0 := by
    change (T.levyMeasure.restrict (Iic (-(((n : ℝ) + 1)⁻¹)))) (Ici (0 : ℝ)) = 0
    rw [Measure.restrict_apply measurableSet_Ici]
    exact measure_mono_null inter_subset_left hneg
  have hlaw (n : ℕ) := @source_result81_finite_triplet_transform_law
    (ν n) (hfin n) (hn n) T.drift σ T.gaussianVariance t hσ
  choose μs hchar hreal using hlaw
  refine ⟨μs, ?_, ?_⟩
  · intro ξ
    have hj := hlim ℂ (levyCompensatedIntegrand ξ)
      (integrable_levyCompensatedIntegrand T.levyMeasure_isLevyMeasure ξ)
    simp_rw [hchar, Kyprianou.Ch01.levyTripleExponent]
    exact (Complex.continuous_exp.tendsto _).comp ((hj.const_add _).const_mul _)
  · intro β hβ
    let F (y : ℝ) := Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)
    have hj := hlim ℝ F (source_result81_compensated_real_integrable T.levyMeasure
      T.levyMeasure_isLevyMeasure hneg β hβ)
    refine ⟨fun n => (hreal n β hβ).1, ?_⟩
    have htransform (n : ℕ) : (∫ x, Real.exp (β * x) ∂(μs n : Measure ℝ)) =
        Real.exp ((t : ℝ) * tripletLaplace (-T.drift) σ (ν n) β) := (hreal n β hβ).2
    simp_rw [htransform, tripletLaplace]
    exact (Real.continuous_exp.tendsto _).comp ((hj.const_add _).const_mul _)
