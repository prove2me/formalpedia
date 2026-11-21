-- Prove2me | solution 2 for NewtonianLipschitz.dominantRowNumerator_le_diagonal_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:32.402113+00:00
-- url     : https://prove2.me/submissions/d89bab28-4054-4a84-a54a-f835b558c7cd

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v t : ℝ) (ht : 0 ≤ t)
    (hsq : 2 * t ^ 2 = u ^ 2 + v ^ 2) :
    dominantRowNumerator u v ≤ dominantRowNumerator t t := by
  have hsquares : (u + v) ^ 2 ≤ (2 * t) ^ 2 := by
    nlinarith [sq_nonneg (u - v)]
  have hsum : u + v ≤ 2 * t := by
    by_contra h
    have hstrict : 2 * t < u + v := lt_of_not_ge h
    have hplus : 0 < u + v + 2 * t := by linarith
    have hprod : 0 < (u + v - 2 * t) * (u + v + 2 * t) :=
      mul_pos (sub_pos.mpr hstrict) hplus
    nlinarith [hprod]
  unfold dominantRowNumerator
  nlinarith
end NewtonianLipschitz
