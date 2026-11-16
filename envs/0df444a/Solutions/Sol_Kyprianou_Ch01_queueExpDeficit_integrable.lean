-- Prove2me | solution 1 for Kyprianou.Ch01.queueExpDeficit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:29:02.334816+00:00
-- url     : https://prove2.me/submissions/d75183b8-8b28-49f8-9fb2-a540eae0a9c8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
set_option autoImplicit false

theorem solution
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (theta : ℝ) (ht : 0 ≤ theta) :
    Integrable (fun z : ℝ => 1 - Real.exp (-theta * z)) F := by
  have hae : ∀ᵐ z ∂F, 0 < z := by
    apply (ae_iff).2
    have hz : F {z : ℝ | z ≤ 0} = 0 := hpositive
    simpa only [not_lt] using hz
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hae] with z hz
  have he : Real.exp (-theta * z) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hp := Real.exp_pos (-theta * z)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith
