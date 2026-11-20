-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneProductBoundaryZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:01:22.402934+00:00
-- url     : https://prove2.me/submissions/7ace72c6-363f-45b4-ad36-bfac9587a7bc

import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryPositiveLimit
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryAtInfinity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- The true boundary product vanishes at both ends of the positive half-line. -/
theorem solution (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    Tendsto
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) ∧
    Tendsto
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
  have hpos := Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryPositiveLimit
    alpha ha1 ha2
  have hinfty := Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryAtInfinity
    alpha ha1 ha2
  have hscale (r : ℝ) :
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) =
      (-(alpha : ℂ))⁻¹ *
        ((Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha) : ℝ)) : ℂ)) := by
    push_cast
    ring
  have hEq :
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ)) =
      (fun r : ℝ => (-(alpha : ℂ))⁻¹ *
        ((Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) * (((r ^ (-alpha) : ℝ)) : ℂ))) :=
    funext hscale
  rw [hEq]
  have hconstPos :
      Tendsto (fun _ : ℝ => (-(alpha : ℂ))⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds ((-(alpha : ℂ))⁻¹)) :=
    tendsto_const_nhds
  have hconstInf :
      Tendsto (fun _ : ℝ => (-(alpha : ℂ))⁻¹)
        Filter.atTop (nhds ((-(alpha : ℂ))⁻¹)) :=
    tendsto_const_nhds
  constructor
  · simpa only [mul_zero] using hconstPos.mul hpos
  · simpa only [mul_zero] using hconstInf.mul hinfty
