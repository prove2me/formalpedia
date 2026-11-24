-- Prove2me | solution 1 for Matrix.l2_opNorm_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:50:07.345558+00:00
-- url     : https://prove2.me/submissions/a184b2ee-6daa-475e-814c-429d865c0773

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
theorem _root_.solution [DecidableEq m] (A : Matrix m n ℝ) : ‖Aᵀ‖ = ‖A‖ := by
  rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
end Matrix
