-- Prove2me | solution 1 for LinearMap.det_eq_prod_of_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:26.71922+00:00
-- url     : https://prove2.me/submissions/08488be2-3bbf-42d7-a8e8-de97ce52b6ca

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
theorem _root_.solution {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M) (T : M →ₗ[R] M)
    (μ : ι → R) (h : ∀ i, T (b i) = μ i • b i) :
    LinearMap.det T = ∏ i, μ i := by
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b T = Matrix.diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply, h j, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]
  rw [hmat, Matrix.det_diagonal]
end LinearMap
