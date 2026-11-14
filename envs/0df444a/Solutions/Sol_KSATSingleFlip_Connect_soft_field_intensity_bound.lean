-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_intensity_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:25:57.0486+00:00
-- url     : https://prove2.me/submissions/cdb8ba10-6a52-45fc-8b7b-d1d04e0b428c

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (z : ℝ) : wInt z ≤ 2*Real.cosh z := by
  have he : 0 < Real.exp z := Real.exp_pos _
  have he0 : Real.exp z ≠ 0 := ne_of_gt he
  have he2 : Real.exp (2*z) = (Real.exp z)^2 := by
    rw [show 2*z = z+z by ring, Real.exp_add]
    ring
  unfold wInt
  rw [he2, Real.cosh_eq, Real.exp_neg]
  have heinv : 0 < (Real.exp z)⁻¹ := inv_pos.mpr he
  have ht : 0 ≤ 2*((Real.exp z+(Real.exp z)⁻¹)/2) := by positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨ht,?_⟩
  field_simp
  nlinarith [sq_nonneg (Real.exp z)]
