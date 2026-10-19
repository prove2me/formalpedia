-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exp_neg_stieltjesPhase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/ea04dbd0-3d67-4de6-930e-bd7169c2ed8b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ t ∂μ, 0 < t) :
    Integrable (fun t : ℝ => Real.exp (-stieltjesPhase a b t)) μ := by
  have hterm (i : Fin (r + 1)) :
      Integrable (fun t : ℝ =>
        lagrangeWeight a b i *
          (t / (t + quadraticCoordinate (a i)))) μ :=
    (stieltjesKernel_integrable μ (h.ambient_quadratic_nonneg i)
      hpositive).const_mul _
  apply (integrable_finsetSum _ (fun i _ => hterm i)).congr
  filter_upwards [hpositive] with t ht
  exact (exp_neg_stieltjesPhase_eq_lagrange_sum h ht).symm
end MetricCodes.Spherical.HigherHierarchy
