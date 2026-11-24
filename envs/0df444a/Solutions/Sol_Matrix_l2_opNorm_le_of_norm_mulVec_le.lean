-- Prove2me | solution 1 for Matrix.l2_opNorm_le_of_norm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:28.55556+00:00
-- url     : https://prove2.me/submissions/9e83f4c8-369b-4708-93e1-5f01f0c1d140

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
theorem _root_.solution (A : Matrix m n ℝ) (hC : 0 ≤ C)
    (h : ∀ v : EuclideanSpace ℝ n, ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ v)‖ ≤ C * ‖v‖) :
    ‖A‖ ≤ C := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h
end Matrix
