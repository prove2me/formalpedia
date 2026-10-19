-- Prove2me | solution 1 for NewtonGravitation.shell_angular_primitive_deriv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:32:05.600021+00:00
-- url     : https://prove2.me/submissions/801d0915-6a9d-4bf8-a8b2-3f660c4ec441

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open NewtonGravitation

theorem solution
    (R r t : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hD : 0 < R ^ 2 + r ^ 2 - 2 * R * r * t) :
    HasDerivAt
      (fun u : ℝ =>
        ((R ^ 2 - r ^ 2) / Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u) -
          Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u)) / (4 * R ^ 2 * r))
      ((R - r * t) /
        (2 * (Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t)) ^ 3)) t := by
  set D := R ^ 2 + r ^ 2 - 2 * R * r * t with hDdef
  have hlin : HasDerivAt (fun u : ℝ => R ^ 2 + r ^ 2 - 2 * R * r * u) (-(2 * R * r)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * R * r)).const_sub (R ^ 2 + r ^ 2)
    simpa using this
  have hs : HasDerivAt (fun u : ℝ => Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u))
      (-(2 * R * r) / (2 * Real.sqrt D)) t := hlin.sqrt hD.ne'
  have hsq : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hF := (((hasDerivAt_const t (R ^ 2 - r ^ 2)).div hs hsq.ne').sub hs).div_const (4 * R ^ 2 * r)
  refine hF.congr_deriv ?_
  have hD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  rw [show Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t) = Real.sqrt D from rfl]
  set s := Real.sqrt D
  rw [hDdef] at hD2
  field_simp
  linear_combination (2 * R * r) * hD2
