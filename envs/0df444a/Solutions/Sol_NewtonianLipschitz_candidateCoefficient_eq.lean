-- Prove2me | solution 1 for NewtonianLipschitz.candidateCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:20:27.633641+00:00
-- url     : https://prove2.me/submissions/1cba895f-7de3-4eb3-a27c-58991e9c90a6

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (t : ℝ) :
    candidateCoefficient t =
      (2 + 6 * t - 2 * t ^ 2) /
        (Real.sqrt (1 + 2 * t ^ 2)) ^ 5 := by
  rfl
end NewtonianLipschitz
