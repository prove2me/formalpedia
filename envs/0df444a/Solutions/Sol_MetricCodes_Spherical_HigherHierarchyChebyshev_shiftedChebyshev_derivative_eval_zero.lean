-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.shiftedChebyshev_derivative_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/020c21e4-4140-4da6-8b4f-54edbaf2549c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_lt_pi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_affinePolynomial_eval_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    {N j : ℕ} (hjpos : 0 < j) (hj : j < N) :
    (shiftedChebyshev R N).derivative.eval (zero R N j) = 0 := by
  have hN : 0 < N := hjpos.trans hj
  have hsine : 0 < Real.sin (zeroAngle N j) :=
    Real.sin_pos_of_pos_of_lt_pi (zeroAngle_pos hN hjpos)
      (zeroAngle_lt_pi hN hj)
  have hmul : (N : ℝ) * zeroAngle N j = (j : ℝ) * Real.pi := by
    unfold zeroAngle
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hu := Polynomial.Chebyshev.U_real_cos
    (zeroAngle N j) ((N : ℤ) - 1)
  have harg : ((((N : ℤ) - 1 : ℤ) : ℝ) + 1) * zeroAngle N j =
      (j : ℝ) * Real.pi := by
    norm_num
    exact hmul
  rw [harg, Real.sin_nat_mul_pi] at hu
  have hU :
      (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 1)).eval
        (Real.cos (zeroAngle N j)) = 0 :=
    (mul_eq_zero.mp hu).resolve_right hsine.ne'
  unfold shiftedChebyshev
  rw [Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_comp,
    affinePolynomial_eval_zero hR]
  rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul]
  simp [hU]
end MetricCodes.Spherical.HigherHierarchyChebyshev
