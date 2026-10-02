-- Prove2me | solution 1 for MilnorDynamics.exp_cayley_image_exterior_on_disc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T21:06:52.332143+00:00
-- url     : https://prove2.me/submissions/4feea3d4-f819-4401-bf80-bcc1e933bf4d

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_cayley_disk_lt_halfplane

open scoped OnePoint
open Filter Set
open Complex
open MilnorDynamics

/-- On the unit disc, the Cayley-exponential composite has modulus greater than one: the modulus
of an exponential is the exponential of the real part, and the Cayley transform of a point of the
disc has strictly positive real part. -/
theorem solution : ∀ z : ℂ, z ∈ Metric.ball 0 1 → 1 < ‖Complex.exp ((z + 1) / (1 - z))‖ := by
  intro z hz
  have hre : 0 < ((z + 1) / (1 - z)).re := cayley_disk_lt_halfplane z hz
  rw [Complex.norm_exp]
  have h1 : (1 : ℝ) < Real.exp ((z + 1) / (1 - z)).re := by
    have := Real.exp_lt_exp.mpr hre
    rwa [Real.exp_zero] at this
  exact h1
