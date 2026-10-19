-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/30825205-49b5-4cd4-8d79-53826fc0599c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_sum_lagrangeWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exp_neg_stieltjesPhase_eq_lagrange_sum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesKernel_integrable

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (hstieltjes : ∀ i : Fin (r + 1),
      (∫ t : ℝ, t / (t + quadraticCoordinate (a i)) ∂μ) =
        1 - 2 * spectralAtom (a i)) :
    (∫ t : ℝ, Real.exp (-stieltjesPhase a b t) ∂μ) =
      1 - 2 * Gamma a b := by
  have hterm (i : Fin (r + 1)) :
      Integrable (fun t : ℝ =>
        lagrangeWeight a b i *
          (t / (t + quadraticCoordinate (a i)))) μ :=
    (stieltjesKernel_integrable μ (h.ambient_quadratic_nonneg i)
      hpositive).const_mul _
  calc
    (∫ t : ℝ, Real.exp (-stieltjesPhase a b t) ∂μ) =
        ∫ t : ℝ, ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (t / (t + quadraticCoordinate (a i))) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpositive] with t ht
          exact exp_neg_stieltjesPhase_eq_lagrange_sum h ht
    _ = ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (∫ t : ℝ, t / (t + quadraticCoordinate (a i)) ∂μ) := by
          rw [integral_finsetSum _ (fun i _ => hterm i)]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]
    _ = ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (1 - 2 * spectralAtom (a i)) := by
          congr 1
          funext i
          rw [hstieltjes i]
    _ = 1 - 2 * Gamma a b := by
          unfold Gamma
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib, h.sum_lagrangeWeight]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
end MetricCodes.Spherical.HigherHierarchy
