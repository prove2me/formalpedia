-- Prove2me | solution 1 for Matrix.IsHermitian.l2_opNorm_le_of_abs_eigenvalues_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:18.240059+00:00
-- url     : https://prove2.me/submissions/8ede80cb-c60f-4943-b317-5d43661140e6

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
theorem _root_.solution [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ i, |hA.eigenvalues i| ≤ c) : ‖A‖ ≤ c := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (Classical.arbitrary n))
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg hc0]
  intro i
  simpa using hc i
end Matrix.IsHermitian
