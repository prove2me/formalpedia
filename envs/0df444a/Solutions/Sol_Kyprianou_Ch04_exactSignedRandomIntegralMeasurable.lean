-- Prove2me | solution 1 for Kyprianou.Ch04.exactSignedRandomIntegralMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:43:37.630582+00:00
-- url     : https://prove2.me/submissions/166c3ffe-9d3d-4571-9fb3-4d2a036db8b8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_integrableIffFiniteSignedParts
open MeasureTheory Filter
open scoped ENNReal Classical
set_option autoImplicit false

/-- Exact signed random-integral measurability, including nonintegrable outcomes. -/
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (R : Omega → Measure E) (f : Omega → E → Real)
    (hf : ∀ w, Measurable (f w))
    (hLp : Measurable (fun w => ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w)))
    (hLn : Measurable (fun w => ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w))) :
    StronglyMeasurable (fun w => ∫ z, f w z ∂(R w)) := by
  let Lp (w : Omega) := ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w)
  let Ln (w : Omega) := ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w)
  have heq : (fun w => ∫ z, f w z ∂(R w)) =
      fun w => if Lp w < ⊤ ∧ Ln w < ⊤ then (Lp w).toReal - (Ln w).toReal else 0 := by
    funext w
    have hi := Kyprianou.Ch04.integrableIffFiniteSignedParts (R w) (f w) (hf w)
    by_cases h : Lp w < ⊤ ∧ Ln w < ⊤
    · rw [if_pos h, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hi.2 h)]
      simp [Lp, Ln, ENNReal.ofReal_max]
    · rw [if_neg h, integral_undef (fun hh => h (hi.1 hh))]
  rw [heq]
  have hLpm : Measurable Lp := hLp
  have hLnm : Measurable Ln := hLn
  exact (Measurable.ite
    ((measurableSet_lt hLpm measurable_const).inter (measurableSet_lt hLnm measurable_const))
    (hLpm.ennreal_toReal.sub hLnm.ennreal_toReal) measurable_const).stronglyMeasurable
