-- Prove2me | solution 1 for Matrix.IsHermitian.ciSup_eigenvalues_le_l2_opNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:23.853471+00:00
-- url     : https://prove2.me/submissions/7199ee77-9359-4bd0-81d2-8ce6ad975cee

module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian

set_option autoImplicit true
@[expose] public section
public section
open Matrix Matrix.IsHermitian
open scoped Matrix Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
namespace Matrix.IsHermitian
theorem _root_.solution [Nonempty n] (hA : A.IsHermitian) :
    ⨆ i, hA.eigenvalues i ≤ ‖A‖ := by
  refine ciSup_le fun i ↦ ?_
  have hb : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h := l2_opNorm_mulVec A (hA.eigenvectorBasis i)
  rw [hA.mulVec_eigenvectorBasis i, hb, mul_one] at h
  exact (le_abs_self _).trans (by simpa [norm_smul, hb] using h)
end Matrix.IsHermitian
