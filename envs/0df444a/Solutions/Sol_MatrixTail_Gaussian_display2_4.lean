-- Prove2me | solution 1 for MatrixTail.Gaussian.display2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:24:33.925424+00:00
-- url     : https://prove2.me/submissions/0580c799-c9f9-492e-8971-9d90c8f42668

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

theorem solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    cfc Real.cosh A ≤ MatrixTail.Master.mexp ((1 / 2 : ℝ) • A ^ 2) := by
  have hsa : IsSelfAdjoint A := hA
  have h2 : cfc (fun x : ℝ => (1 / 2) * x ^ 2) A = (1 / 2 : ℝ) • A ^ 2 := by
    have := cfc_const_mul (1 / 2 : ℝ) (fun x : ℝ => x ^ 2) A (by fun_prop)
    rw [cfc_pow_id A 2 hsa] at this
    exact this
  unfold MatrixTail.Master.mexp
  rw [← h2, ← cfc_comp Real.exp (fun x : ℝ => (1 / 2) * x ^ 2) A hsa
    (Real.continuous_exp.continuousOn) (by fun_prop)]
  apply cfc_mono
  · intro x hx
    have := Real.cosh_le_exp_half_sq x
    simpa [Function.comp, div_eq_inv_mul] using this
  · exact Real.continuous_cosh.continuousOn
  · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
