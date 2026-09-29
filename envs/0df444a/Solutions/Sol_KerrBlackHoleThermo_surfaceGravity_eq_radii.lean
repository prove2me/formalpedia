-- Prove2me | solution 1 for KerrBlackHoleThermo.surfaceGravity_eq_radii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T15:34:53.447088+00:00
-- url     : https://prove2.me/submissions/0adfb35e-13e3-4d78-ac9e-e6c3e8a428d2

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
    surfaceGravity M a = (rPlus M a - rMinus M a) / (2 * (rPlus M a ^ 2 + a ^ 2)) := by
  rw [kerrP2M_rPlus_sq_add M a ha]
  have hs0 : 0 ≤ √(M ^ 2 - a ^ 2) := Real.sqrt_nonneg _
  have hpos : 0 < M + √(M ^ 2 - a ^ 2) := by linarith
  unfold surfaceGravity rPlus rMinus
  field_simp
  ring
