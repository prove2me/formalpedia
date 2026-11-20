-- Prove2me | solution 1 for Kyprianou.Ch01.stableCompensatedFourierNumeratorDerivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:59:47.899179+00:00
-- url     : https://prove2.me/submissions/36c1945c-eab2-4e13-a944-4d6a1423a974

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Complex
set_option autoImplicit false

/-- Real derivative of the compensated imaginary-exponential numerator. -/
theorem solution (r : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        Complex.exp (Complex.I * (t : ℂ)) - 1 -
          Complex.I * (t : ℂ))
      (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) r := by
  have ha : HasDerivAt
      (fun z : ℂ => Complex.I * z) Complex.I (r : ℂ) := by
    simpa using (hasDerivAt_id (r : ℂ)).const_mul Complex.I
  have hb : HasDerivAt
      (fun z : ℂ => Complex.exp (Complex.I * z))
      (Complex.exp (Complex.I * (r : ℂ)) * Complex.I)
      (r : ℂ) := ha.cexp
  have hexp : HasDerivAt
      (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)))
      (Complex.exp (Complex.I * (r : ℂ)) * Complex.I) r :=
    hb.comp_ofReal
  have hlin : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ))
      Complex.I r := ha.comp_ofReal
  have hder := (hexp.sub_const (1 : ℂ)).sub hlin
  convert hder using 1 <;>
    first
    | rfl
    | (funext t; dsimp [Pi.sub_apply]; ring)
    | ring
