-- Prove2me | solution 1 for Lean4LPD.schur_row_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:03:10.746185+00:00
-- url     : https://prove2.me/submissions/d4f5cd63-0adb-431d-b2f2-e691bb4eccbe

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
omit [Fintype ι]
namespace Lean4LPD
theorem _root_.solution (A : Matrix ι κ 𝕜) (y : κ → 𝕜) (i : ι) (R : ℝ)
    (hrow : ∑ j, ‖A i j‖ ≤ R) :
    ‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by
  have habs : ‖(A *ᵥ y) i‖ ≤ ∑ j, ‖A i j‖ * ‖y j‖ := by
    simpa only [Matrix.mulVec, dotProduct, norm_mul] using
      (norm_sum_le univ (fun j => A i j * y j))
  have hcs : (∑ j, ‖A i j‖ * ‖y j‖) ^ 2 ≤
      (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul univ
      (f := fun j => ‖A i j‖) (g := fun j => ‖A i j‖ * ‖y j‖ ^ 2)
    · intro j _; exact norm_nonneg _
    · intro j _; positivity
    · intro j _; exact le_of_eq (by ring)
  exact ((pow_le_pow_left₀ (norm_nonneg _) habs 2).trans hcs).trans
    (mul_le_mul_of_nonneg_right hrow (Finset.sum_nonneg fun j _ => by positivity))
end Lean4LPD
