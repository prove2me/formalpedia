-- Prove2me | solution 1 for NewtonianLipschitz.dominantRowNumerator_le_diagonal_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:43.913644+00:00
-- url     : https://prove2.me/submissions/74194856-b110-4b43-aa85-356c5817da9e

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

private theorem diagonal_bound (u v t : ℝ) (ht : 0 ≤ t)
    (hsq : 2 * t ^ 2 = u ^ 2 + v ^ 2) : dominantRowNumerator u v ≤ dominantRowNumerator t t := by
  have hs : u + v ≤ 2 * t := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < u + v + 2 * t by linarith)
    nlinarith [sq_nonneg (u - v)]
  unfold dominantRowNumerator
  nlinarith

theorem solution
    (u v t : ℝ) (ht : 0 ≤ t)
    (hsq : 2 * t ^ 2 = u ^ 2 + v ^ 2) :
    dominantRowNumerator u v ≤ dominantRowNumerator t t := by
  exact diagonal_bound u v t ht hsq
