-- Prove2me | solution 1 for Matrix.IsHermitian.le_ciSup_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:20.965803+00:00
-- url     : https://prove2.me/submissions/c3be63cc-74e9-4c7f-b0fe-7a296114fd37

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
theorem _root_.solution (hA : A.IsHermitian) {μ : ℝ} {v : n → ℝ} (hv : v ≠ 0)
    (hev : A *ᵥ v = μ • v) : μ ≤ ⨆ i, hA.eigenvalues i := by
  have hmem : μ ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hev), hv⟩
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, rfl⟩ := hmem
  exact le_ciSup (Finite.bddAbove_range _) i
end Matrix.IsHermitian
