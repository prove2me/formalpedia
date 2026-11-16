-- Prove2me | solution 1 for Kyprianou.Ch01.expDeficit_hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:20:58.765885+00:00
-- url     : https://prove2.me/submissions/4b7e10ab-2ff8-43e1-88ff-7b4bada9b446

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem solution (x : ℝ) :
    HasDerivAt (fun theta : ℝ => 1 - Real.exp (-theta * x)) x 0 := by
  have hlin : HasDerivAt (fun theta : ℝ => -theta * x) (-x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).neg).mul_const x
  have hh := (Real.hasDerivAt_exp (-(0 : ℝ) * x)).comp (0 : ℝ) hlin
  have he : HasDerivAt (fun theta : ℝ => Real.exp (-theta * x)) (-x) 0 := by
    convert hh using 1 <;> (first | rfl | simp [Real.exp_zero] | ring)
  have hh' := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub he
  convert hh' using 1 <;> (first | rfl | simp [Real.exp_zero] | ring)
