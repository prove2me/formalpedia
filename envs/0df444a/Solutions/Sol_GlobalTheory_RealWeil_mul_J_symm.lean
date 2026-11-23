-- Prove2me | solution 1 for GlobalTheory.RealWeil.mul_J_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:53.040317+00:00
-- url     : https://prove2.me/submissions/87f919e4-e108-43e2-8d98-46538ac46032

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    (X * Matrix.J l ℝ)ᵀ = X * Matrix.J l ℝ := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have h2 := congrArg (fun Y => Matrix.J l ℝ * Y * Matrix.J l ℝ) h
  simp only [Matrix.mul_assoc, J_squared] at h2
  simp only [← Matrix.mul_assoc, J_squared] at h2
  rw [transpose_mul, J_transpose]
  simpa using h2
end GlobalTheory.RealWeil
