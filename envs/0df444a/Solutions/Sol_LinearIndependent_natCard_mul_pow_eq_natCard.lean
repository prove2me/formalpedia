-- Prove2me | solution 1 for LinearIndependent.natCard_mul_pow_eq_natCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:39.904812+00:00
-- url     : https://prove2.me/submissions/98434913-1377-44ab-a324-6b5fa55b74c5

module
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LinearMap_Card
section
public section
open Module
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {r : ℕ} {v : Fin r → V}
private lemma LinearIndependent.exists_linearMap_apply_eq (hv : LinearIndependent K v)
    (w : Fin r → W) : ∃ A : V →ₗ[K] W, ∀ i, A (v i) = w i := by
  obtain ⟨A, hA⟩ := LinearMap.exists_extend ((Basis.span hv).constr K w)
  use A
  intro i
  simpa [Finsupp.single_apply] using congr($hA (Basis.span hv i))
private lemma LinearIndependent.surjective_pi_applyₗ (hv : LinearIndependent K v) :
    Function.Surjective
      (LinearMap.pi fun i ↦ LinearMap.applyₗ (v i) : (V →ₗ[K] W) →ₗ[K] Fin r → W) := by
  intro w
  obtain ⟨A, hA⟩ := hv.exists_linearMap_apply_eq w
  exact ⟨A, funext hA⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
open Module
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {r : ℕ} {v : Fin r → V}
namespace LinearIndependent
theorem _root_.solution (hv : LinearIndependent K v) :
    Nat.card {A : V →ₗ[K] W // ∀ i, A (v i) = 0} * Nat.card W ^ r = Nat.card (V →ₗ[K] W) := by
  let f := (LinearMap.pi fun i ↦
    LinearMap.applyₗ (v i) : (V →ₗ[K] W) →ₗ[K] Fin r → W).toAddMonoidHom
  have h := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hv.surjective_pi_applyₗ,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (Fin r → W)) ≃+ (Fin r → W)).toEquiv] at h
  convert h using 2
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun A ↦ by simp [funext_iff, f, LinearMap.pi_apply])
  · rw [Nat.card_fun, Nat.card_fin]
end LinearIndependent
