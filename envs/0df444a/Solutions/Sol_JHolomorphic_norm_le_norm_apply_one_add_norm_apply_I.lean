-- Prove2me | solution 1 for JHolomorphic.norm_le_norm_apply_one_add_norm_apply_I
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:26:11.951702+00:00
-- url     : https://prove2.me/submissions/e005bd43-d0c6-4c53-9051-a21e27d76ace

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem norm_le_norm_apply_one_add_norm_apply_I_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℂ →L[ℝ] F) : ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]; exact (Complex.re_add_im w).symm
  rw [hw, map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |w.re| ≤ ‖w.re • (1 : ℂ) + w.im • Complex.I‖ := by
    rw [← hw]; exact Complex.abs_re_le_norm w
  have h2 : |w.im| ≤ ‖w.re • (1 : ℂ) + w.im • Complex.I‖ := by
    rw [← hw]; exact Complex.abs_im_le_norm w
  nlinarith [norm_nonneg (T 1), norm_nonneg (T Complex.I), abs_nonneg w.re, abs_nonneg w.im]


end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℂ →L[ℝ] F) : ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ :=
  norm_le_norm_apply_one_add_norm_apply_I_aux T
