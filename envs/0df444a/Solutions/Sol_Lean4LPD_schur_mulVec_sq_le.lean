-- Prove2me | solution 1 for Lean4LPD.schur_mulVec_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:21.808794+00:00
-- url     : https://prove2.me/submissions/aaa0758a-ac82-4b88-9130-3b555d714e85

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Theorems.Thm_Lean4LPD_schur_row_sq_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace Lean4LPD
theorem _root_.solution (A : Matrix ι κ 𝕜) (y : κ → 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤ R * C * ∑ j, ‖y j‖ ^ 2 := by
  have h1 : (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤
      ∑ i, R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => schur_row_sq_le A y i R (hrow i)
  have h2 : (∑ i, R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2) =
      R * ∑ j, (∑ i, ‖A i j‖) * ‖y j‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  calc (∑ i, ‖(A *ᵥ y) i‖ ^ 2)
      ≤ R * ∑ j, (∑ i, ‖A i j‖) * ‖y j‖ ^ 2 := h1.trans_eq h2
    _ ≤ R * ∑ j, C * ‖y j‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)) hR
    _ = R * C * ∑ j, ‖y j‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]
end Lean4LPD
