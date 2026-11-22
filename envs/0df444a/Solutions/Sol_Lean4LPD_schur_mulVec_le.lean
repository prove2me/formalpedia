-- Prove2me | solution 1 for Lean4LPD.schur_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:56.389693+00:00
-- url     : https://prove2.me/submissions/ebd4d91d-e613-4ed8-aa5e-1d65f07a098a

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Theorems.Thm_Lean4LPD_schur_clm_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq κ]
omit [DecidableEq κ]
namespace Lean4LPD
theorem _root_.solution (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖toLp 2 (A *ᵥ y.ofLp)‖ ≤ Real.sqrt (R * C) * ‖y‖ := by
  classical
  exact schur_clm_le A y hR hC hrow hcol
end Lean4LPD
