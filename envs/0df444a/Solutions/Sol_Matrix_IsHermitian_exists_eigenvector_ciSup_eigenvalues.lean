-- Prove2me | solution 1 for Matrix.IsHermitian.exists_eigenvector_ciSup_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:25.574547+00:00
-- url     : https://prove2.me/submissions/c3465337-7b53-4fe1-ac84-567ea8367725

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
    ∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = (⨆ i, hA.eigenvalues i) • v := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := hA.eigenvalues)
  refine ⟨⇑(hA.eigenvectorBasis i),
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i, ?_⟩
  rw [← hi]
  exact hA.mulVec_eigenvectorBasis i
end Matrix.IsHermitian
