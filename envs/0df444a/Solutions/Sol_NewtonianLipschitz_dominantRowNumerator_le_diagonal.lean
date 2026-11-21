-- Prove2me | solution 1 for NewtonianLipschitz.dominantRowNumerator_le_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:43.896114+00:00
-- url     : https://prove2.me/submissions/c0c97aa7-c9cd-4a53-83c6-a457855d4e5e

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

theorem solution (u v : ℝ) :
    dominantRowNumerator u v ≤
      dominantRowNumerator (diagonalParameter u v) (diagonalParameter u v) := by
  apply diagonal_bound
  · exact Real.sqrt_nonneg _
  · unfold diagonalParameter
    have h : 0 ≤ (u ^ 2 + v ^ 2) / 2 := by positivity
    linarith [Real.sq_sqrt h]
