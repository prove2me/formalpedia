-- Prove2me | solution 2 for NewtonianLipschitz.dominantRowNumerator_le_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:57.198862+00:00
-- url     : https://prove2.me/submissions/d0b27b65-9610-412c-9a9a-37b667432f3f

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Theorems.Thm_NewtonianLipschitz_diagonalParameter_sq
public import Theorems.Thm_NewtonianLipschitz_dominantRowNumerator_le_diagonal_of_sq

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (u v : ℝ) :
    dominantRowNumerator u v ≤
      dominantRowNumerator (diagonalParameter u v) (diagonalParameter u v) := by
  obtain ⟨ht, hsq⟩ := diagonalParameter_sq u v
  exact dominantRowNumerator_le_diagonal_of_sq u v (diagonalParameter u v) ht hsq
end NewtonianLipschitz
