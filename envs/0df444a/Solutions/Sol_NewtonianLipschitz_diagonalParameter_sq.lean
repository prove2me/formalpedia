-- Prove2me | solution 1 for NewtonianLipschitz.diagonalParameter_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:25:51.129199+00:00
-- url     : https://prove2.me/submissions/cdb62b30-7472-4236-9a4b-f9eff3e7e799

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (u v : ℝ) :
    0 ≤ diagonalParameter u v ∧
      2 * (diagonalParameter u v) ^ 2 = u ^ 2 + v ^ 2 := by
  have hnonneg : 0 ≤ (u ^ 2 + v ^ 2) / (2 : ℝ) := by positivity
  constructor
  · exact Real.sqrt_nonneg _
  · unfold diagonalParameter
    rw [Real.sq_sqrt hnonneg]
    ring
end NewtonianLipschitz
