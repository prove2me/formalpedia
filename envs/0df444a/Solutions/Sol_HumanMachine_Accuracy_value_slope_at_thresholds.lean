-- Prove2me | solution 1 for HumanMachine.Accuracy.value_slope_at_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:44:33.78216+00:00
-- url     : https://prove2.me/submissions/89534607-d588-4756-90c2-91745551c825

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

set_option autoImplicit false

theorem solution (lam : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun μ : ℝ => lam * (Real.log (Real.exp (1 / lam) + 1) - Real.binEntropy μ))
        (-1) (HumanMachine.Alone.muLow lam) ∧
      HasDerivAt (fun μ : ℝ => lam * (Real.log (Real.exp (1 / lam) + 1) - Real.binEntropy μ))
        1 (HumanMachine.Alone.muHigh lam) := by
  set E := Real.exp (1 / lam) with hE
  have hE1 : 1 < E := by
    rw [hE]; calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < _ := Real.exp_lt_exp.mpr (by positivity)
  have hE0 : 0 < E := by linarith
  have hlogE : Real.log E = 1 / lam := Real.log_exp _
  have hEp : 0 < E + 1 := by linarith
  have key : ∀ x : ℝ, x ≠ 0 → x ≠ 1 →
      HasDerivAt (fun μ : ℝ => lam * (Real.log (E + 1) - Real.binEntropy μ))
        (-lam * (Real.log (1 - x) - Real.log x)) x := by
    intro x h0 h1
    have h := (Real.hasDerivAt_binEntropy h0 h1)
    have h2 := ((hasDerivAt_const x (Real.log (E + 1))).sub h).const_mul lam
    exact h2.congr_deriv (by ring)
  constructor
  · have h0 : HumanMachine.Alone.muLow lam ≠ 0 := by
      unfold HumanMachine.Alone.muLow; rw [← hE]; positivity
    have h1 : HumanMachine.Alone.muLow lam ≠ 1 := by
      unfold HumanMachine.Alone.muLow; rw [← hE]
      intro h
      rw [div_eq_one_iff_eq hEp.ne'] at h
      linarith
    convert key _ h0 h1 using 1
    have : Real.log (1 - HumanMachine.Alone.muLow lam) - Real.log (HumanMachine.Alone.muLow lam)
        = 1 / lam := by
      unfold HumanMachine.Alone.muLow; rw [← hE]
      have : 1 - 1 / (E + 1) = E / (E + 1) := by field_simp; ring
      rw [this, Real.log_div hE0.ne' hEp.ne', Real.log_div one_ne_zero hEp.ne', hlogE]
      simp only [Real.log_one]; ring
    rw [this]; field_simp
  · have h0 : HumanMachine.Alone.muHigh lam ≠ 0 := by
      unfold HumanMachine.Alone.muHigh; rw [← hE]; positivity
    have h1 : HumanMachine.Alone.muHigh lam ≠ 1 := by
      unfold HumanMachine.Alone.muHigh; rw [← hE]
      intro h
      rw [div_eq_one_iff_eq hEp.ne'] at h
      linarith
    convert key _ h0 h1 using 1
    have : Real.log (1 - HumanMachine.Alone.muHigh lam) - Real.log (HumanMachine.Alone.muHigh lam)
        = -(1 / lam) := by
      unfold HumanMachine.Alone.muHigh; rw [← hE]
      have : 1 - E / (E + 1) = 1 / (E + 1) := by field_simp; ring
      rw [this, Real.log_div one_ne_zero hEp.ne', Real.log_div hE0.ne' hEp.ne', hlogE]
      simp only [Real.log_one]; ring
    rw [this]; field_simp
