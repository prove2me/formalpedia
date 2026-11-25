-- Prove2me | solution 1 for LinearMap.det_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:24:33.626805+00:00
-- url     : https://prove2.me/submissions/1c03e0f2-f6ec-462d-9644-2e454409a5ec

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
namespace LinearMap
theorem _root_.solution (T : E →ₗ[𝕜] E) :
    LinearMap.det (adjoint T) = conj (LinearMap.det T) := by
  set v := stdOrthonormalBasis 𝕜 E with hv
  rw [← LinearMap.det_toMatrix v.toBasis (adjoint T), LinearMap.toMatrix_adjoint v v T,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix v.toBasis T, starRingEnd_apply]
end LinearMap
