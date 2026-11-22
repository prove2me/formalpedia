-- Prove2me | solution 1 for Lean4LPD.schur_clm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:57.781821+00:00
-- url     : https://prove2.me/submissions/cf36f468-2ece-4968-8721-83b9397cf4c3

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Theorems.Thm_Lean4LPD_schur_mulVec_sq_le

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
theorem _root_.solution (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖clm A y‖ ≤ Real.sqrt (R * C) * ‖y‖ := by
  have hsq : ‖clm A y‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC)]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact schur_mulVec_sq_le A y.ofLp hR hrow hcol
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))] at h
end Lean4LPD
