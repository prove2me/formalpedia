-- Prove2me | solution 1 for Matrix.sum_sq_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:51:58.400476+00:00
-- url     : https://prove2.me/submissions/954070b2-e79e-4584-9bff-eb45fc8eac1b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest

set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}
namespace Matrix
theorem _root_.solution (A : Matrix m n ℝ) (v : n → ℝ) :
    ∑ i, (A *ᵥ v) i ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, v j ^ 2 := by
  have h := l2_opNorm_mulVec A ((EuclideanSpace.equiv n ℝ).symm v)
  simpa [mul_pow, EuclideanSpace.norm_sq_eq, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2
end Matrix
