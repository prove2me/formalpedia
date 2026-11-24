-- Prove2me | solution 1 for Matrix.l2_opNorm_le_of_sum_sq_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:05.437425+00:00
-- url     : https://prove2.me/submissions/8335e810-871a-4650-929f-afe9f54c9898

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Theorems.Thm_Matrix_l2_opNorm_le_of_norm_mulVec_le

set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}
namespace Matrix
theorem _root_.solution (A : Matrix m n ℝ) (hC : 0 ≤ C)
    (h : ∀ v : n → ℝ, ∑ i, (A *ᵥ v) i ^ 2 ≤ C ^ 2 * ∑ j, v j ^ 2) :
    ‖A‖ ≤ C :=
  l2_opNorm_le_of_norm_mulVec_le A hC fun v ↦
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg v))).mp <| by
      simpa [EuclideanSpace.norm_sq_eq, mul_pow] using h _
end Matrix
