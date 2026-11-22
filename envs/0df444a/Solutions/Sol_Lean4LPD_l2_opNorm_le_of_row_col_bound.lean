-- Prove2me | solution 1 for Lean4LPD.l2_opNorm_le_of_row_col_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:20.662224+00:00
-- url     : https://prove2.me/submissions/bb7e7cc2-999b-42aa-ab92-75378db75343

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Theorems.Thm_Lean4LPD_l2_opNorm_le_schur

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq κ]
namespace Lean4LPD
theorem _root_.solution (A : Matrix ι κ 𝕜) {B : ℝ}
    (hB : 0 ≤ B) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ B)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ B) : ‖A‖ ≤ B := by
  have h := l2_opNorm_le_schur A hB hB hrow hcol
  simpa only [← sq, Real.sqrt_sq hB] using h
end Lean4LPD
