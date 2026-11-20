-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftExpDerivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:20:30.145229+00:00
-- url     : https://prove2.me/submissions/031b1c6c-0424-4888-9bdd-3c17f5c0d10e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

/-- Real derivative of the complex exponential deficit at any complex rate. -/
theorem solution (w : ℂ) (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.exp (w * (t : ℂ)) - 1)
      (w * Complex.exp (w * (r : ℂ))) r := by
  have ha : HasDerivAt (fun z : ℂ => w * z) w (r : ℂ) := by
    simpa using (hasDerivAt_id (r : ℂ)).const_mul w
  have hb : HasDerivAt (fun z : ℂ => Complex.exp (w * z))
      (Complex.exp (w * (r : ℂ)) * w) (r : ℂ) := ha.cexp
  have hc : HasDerivAt (fun t : ℝ => Complex.exp (w * (t : ℂ)))
      (Complex.exp (w * (r : ℂ)) * w) r := hb.comp_ofReal
  have hd := hc.sub_const (1 : ℂ)
  convert hd using 1 <;>
    first
    | rfl
    | ring
