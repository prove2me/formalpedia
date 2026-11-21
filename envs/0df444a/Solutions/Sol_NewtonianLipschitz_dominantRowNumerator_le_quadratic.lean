-- Prove2me | solution 1 for NewtonianLipschitz.dominantRowNumerator_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:45.079185+00:00
-- url     : https://prove2.me/submissions/03a7e09d-6cc7-4910-bc21-a9010d34d86a

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (u v : ℝ) :
    dominantRowNumerator u v ≤
      (13 : ℝ) / 5 + ((13 : ℝ) / 2) * (u ^ 2 + v ^ 2) := by
  unfold dominantRowNumerator
  nlinarith [sq_nonneg (u - 1 / 5), sq_nonneg (v - 1 / 5)]
end NewtonianLipschitz
