-- Prove2me | solution 1 for NewtonianLipschitz.dominantRowNumerator_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:50.328294+00:00
-- url     : https://prove2.me/submissions/84307011-13fc-4aa9-bec7-c4606b297551

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (t : ℝ) :
    dominantRowNumerator t t = 2 + 6 * t - 2 * t ^ 2 := by
  unfold dominantRowNumerator
  ring
end NewtonianLipschitz
