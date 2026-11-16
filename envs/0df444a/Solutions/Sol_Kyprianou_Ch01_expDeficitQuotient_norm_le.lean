-- Prove2me | solution 1 for Kyprianou.Ch01.expDeficitQuotient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:14:22.354064+00:00
-- url     : https://prove2.me/submissions/a963b7f6-3eff-485b-af02-d9cd159e8e96

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem solution
    (theta x : ℝ) (ht : 0 < theta) (hx : 0 ≤ x) :
    ‖(1 - Real.exp (-theta * x)) / theta‖ ≤ x := by
  have htx : 0 ≤ theta * x := mul_nonneg ht.le hx
  have he : Real.exp (-theta * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have he' : 1 - theta * x ≤ Real.exp (-theta * x) := by
    have h := Real.add_one_le_exp (-theta * x)
    linarith
  have hp : 0 ≤ (1 - Real.exp (-theta * x)) / theta :=
    div_nonneg (by linarith) ht.le
  have hb : (1 - Real.exp (-theta * x)) / theta ≤ x :=
    (div_le_iff₀ ht).mpr (by nlinarith)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hb
