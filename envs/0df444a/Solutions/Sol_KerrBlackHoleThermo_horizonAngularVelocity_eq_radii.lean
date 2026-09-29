-- Prove2me | solution 1 for KerrBlackHoleThermo.horizonAngularVelocity_eq_radii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T15:51:56.878838+00:00
-- url     : https://prove2.me/submissions/b05e6365-68e1-41b0-a373-94b77d5f6d02

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

set_option autoImplicit false

open Real

open KerrBlackHoleThermo in
theorem kerrP2M_rPlus_sq_add (M a : ℝ) (ha : a ^ 2 ≤ M ^ 2) :
    rPlus M a ^ 2 + a ^ 2 = 2 * M * (M + √(M ^ 2 - a ^ 2)) := by
  have hs2 : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  unfold rPlus
  linear_combination hs2

open KerrBlackHoleThermo Real in
theorem solution (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    horizonAngularVelocity M a = a / (rPlus M a ^ 2 + a ^ 2) := by
  have _hM' := hM
  rw [kerrP2M_rPlus_sq_add M a ha]
  rfl
