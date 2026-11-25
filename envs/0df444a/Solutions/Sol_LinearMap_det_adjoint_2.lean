-- Prove2me | solution 2 for LinearMap.det_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:36:55.759331+00:00
-- url     : https://prove2.me/submissions/9299197b-f3ff-4d0a-8a37-c01c35710275

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Determinant
public import Definitions.Def_BasicResults_Determinant
set_option autoImplicit true
@[expose] public section
public section
open LinearMap
open scoped ComplexConjugate
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The determinant of the adjoint of an endomorphism of a finite-dimensional inner product
space is the conjugate of its determinant. -/
theorem solution (T : E →ₗ[𝕜] E) :
    LinearMap.det (adjoint T) = conj (LinearMap.det T) := by
  classical
  set b := stdOrthonormalBasis 𝕜 E with hb
  rw [← LinearMap.det_toMatrix b.toBasis (adjoint T),
      ← LinearMap.det_toMatrix b.toBasis T]
  rw [LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
  rfl
