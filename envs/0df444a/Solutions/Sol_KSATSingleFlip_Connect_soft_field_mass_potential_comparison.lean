-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_mass_potential_comparison
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:35:43.883045+00:00
-- url     : https://prove2.me/submissions/0733e298-4ec8-4c98-a98e-700b75d84174

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_weight_lower_bound
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_bounds
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν] :
    c0*(massM ν).toReal ≤ hPot ν ∧ hPot ν ≤ (massM ν).toReal := by
  refine ⟨?_, (soft_field_potential_bounds ν).2.2⟩
  have hp (z : ℝ) : c0 ≤ Real.cosh z*gW (qOf z) := by
    obtain ⟨hq,hq1,hmass⟩ := soft_field_mass_identity z
    have hh := mul_le_mul_of_nonneg_left (soft_field_weight_lower_bound (qOf z) (le_of_lt hq) (le_of_lt hq1)) (le_of_lt (Real.cosh_pos z))
    calc
      c0 = c0*(Real.cosh z*fW (qOf z)) := by rw [hmass, mul_one]
      _ = Real.cosh z*(c0*fW (qOf z)) := by ring
      _ ≤ Real.cosh z*gW (qOf z) := hh
  have hi := (soft_field_potential_bounds ν).1
  have hh := integral_mono (integrable_const c0) hi hp
  unfold hPot pairing massM
  simpa [measureReal_def, mul_comm] using hh
