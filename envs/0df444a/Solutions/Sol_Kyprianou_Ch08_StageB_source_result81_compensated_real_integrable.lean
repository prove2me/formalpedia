-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_compensated_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:59:24.636084+00:00
-- url     : https://prove2.me/submissions/7823010b-7818-4805-a211-96c73c6b2cc1

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_ConsistentSubmodular_exp_neg_le_quadratic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

private theorem result81_negative_exp_remainder (u : ℝ) (hu : u ≤ 0) :
    ‖Real.exp u - 1 - u‖ ≤ u ^ 2 / 2 := by
  have hupper := ConsistentSubmodular.exp_neg_le_quadratic (neg_nonneg.mpr hu)
  rw [neg_neg] at hupper
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [Real.add_one_le_exp u])]
  nlinarith only [hupper]

private theorem result81_compensated_kernel_bound (β y : ℝ) (hβ : 0 ≤ β) (hy : y < 0) :
    ‖Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)‖ ≤
      max 1 (β ^ 2 / 2) * min 1 (y ^ 2) := by
  have hprod : β * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hy.le
  split_ifs with hs
  · rw [min_eq_right (by nlinarith only [mul_nonneg (show 0 ≤ y + 1 by linarith) (show 0 ≤ 1 - y by linarith)])]
    calc
      _ ≤ (β * y) ^ 2 / 2 := result81_negative_exp_remainder _ hprod
      _ = (β ^ 2 / 2) * y ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg y)
  · rw [min_eq_left (by nlinarith only [mul_nonneg (show 0 ≤ -1 - y by linarith) (show 0 ≤ 1 - y by linarith)]),
      mul_one, sub_zero, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hprod))]
    exact (show -(Real.exp (β * y) - 1) ≤ 1 by linarith only [Real.exp_pos (β * y)]).trans (le_max_left _ _)

theorem solution
    (ν : Measure ℝ) (hν : IsLevyMeasure ν) (hneg : ν (Ici (0 : ℝ)) = 0)
    (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun y => Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)) ν := by
  let g (y : ℝ) := min 1 (y ^ 2)
  have hg : Integrable g ν := ⟨(show Measurable g by fun_prop).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => le_min zero_le_one (sq_nonneg y))).2 hν.2⟩
  have harg : Measurable (fun y : ℝ => β * y) := measurable_const.mul measurable_id
  have hf : Measurable (fun y => Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)) :=
    ((Real.continuous_exp.measurable.comp harg).sub_const 1).sub
      (Measurable.ite measurableSet_Ioi harg measurable_const)
  have hn : ∀ᵐ y ∂ν, y < 0 := by
    apply ae_iff.2
    have hset : {y : ℝ | ¬ y < 0} = Ici (0 : ℝ) := by
      ext y
      change (¬ y < 0) ↔ 0 ≤ y
      exact not_lt
    rw [hset]
    exact hneg
  exact (hg.const_mul (max 1 (β ^ 2 / 2))).mono' hf.aestronglyMeasurable
    (hn.mono fun y hy => result81_compensated_kernel_bound β y hβ hy)
