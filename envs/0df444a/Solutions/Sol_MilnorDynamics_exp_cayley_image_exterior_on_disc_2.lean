-- Prove2me | solution 2 for MilnorDynamics.exp_cayley_image_exterior_on_disc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T21:06:57.893273+00:00
-- url     : https://prove2.me/submissions/64716dde-80de-494a-b72d-d49bc8deb80e

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
  calc 1 < Real.exp ((z + 1) / (1 - z)).re := by
          have := Real.exp_lt_exp.mpr hre
          rwa [Real.exp_zero] at this
    _ = ‖Complex.exp ((z + 1) / (1 - z))‖ := (Complex.norm_exp _).symm
