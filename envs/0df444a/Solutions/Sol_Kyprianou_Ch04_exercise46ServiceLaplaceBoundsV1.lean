-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ServiceLaplaceBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:52:33.301243+00:00
-- url     : https://prove2.me/submissions/5cab6efe-02a2-4539-8035-08233bf329f6

import Mathlib
open MeasureTheory Set
set_option autoImplicit false
theorem solution
    (service : Measure Real) [IsProbabilityMeasure service]
    (hPositive : service (Ioi (0 : Real)) = 1)
    (phi : Real) (hphi : 0 < phi) :
    0 < (∫ y : Real, Real.exp (-phi * y) ∂service) ∧
      (∫ y : Real, Real.exp (-phi * y) ∂service) < 1 := by
  let f : Real → Real := fun y => Real.exp (-phi * y)
  have hp : ∀ᵐ y ∂service, 0 < y :=
    (ae_mem_iff_measure_eq measurableSet_Ioi.nullMeasurableSet).mpr
      (by simpa using hPositive)
  have hlt (y : Real) (hy : 0 < y) : f y < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hphi) hy)
  have hpos (y : Real) : 0 < f y := Real.exp_pos _
  have hf : Integrable f service := by
    apply (integrable_const (1 : Real)).mono
      (by fun_prop : AEStronglyMeasurable f service)
    filter_upwards [hp] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (hpos y), Real.norm_eq_abs, abs_one]
    exact (hlt y hy).le
  have hconst : Integrable (fun _ : Real => (1 : Real)) service :=
    integrable_const 1
  have hsub := hconst.sub hf
  have hfull : Function.support f = univ := by
    ext y
    simp [Function.mem_support, (hpos y).ne']
  have hfirst : 0 < ∫ y, f y ∂service := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => (hpos y).le) hf).mpr
    rw [hfull]
    simp
  have hsecond : 0 < ∫ y, 1 - f y ∂service := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hp.mono fun y hy => sub_nonneg.mpr (hlt y hy).le) hsub).mpr
    have hle : service (Ioi 0) ≤ service (Function.support
        (fun y : Real => 1 - f y)) := by
      apply measure_mono
      intro y hy
      exact sub_ne_zero.mpr (ne_of_gt (hlt y hy))
    rw [hPositive] at hle
    exact zero_lt_one.trans_le hle
  rw [integral_sub hconst hf, integral_const] at hsecond
  simp at hsecond
  exact ⟨hfirst, by linarith⟩
