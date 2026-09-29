-- Prove2me | solution 1 for Module.free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6832dd71-a538-536d-82a8-13248d74f57d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq

set_option autoImplicit false

open scoped TensorProduct

namespace FlatCrit

theorem piScalarRight_one_tmul {A K : Type*} [CommRing A] [Field K] [Algebra A K] {n : ℕ} (x : Fin n → A) (i : Fin n) :
    TensorProduct.piScalarRight A K K (Fin n) ((1 : K) ⊗ₜ[A] x) i = algebraMap A K (x i) := by
  classical
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Algebra.algebraMap_eq_smul_one]

theorem free_of_surjective_of_lTensor_injective
    {A : Type*} [CommRing A] [IsDomain A]
    {C : Type*} [AddCommGroup C] [Module A C] {n : ℕ} (f : (Fin n → A) →ₗ[A] C) (hf : Function.Surjective f)
    (K : Type*) [Field K] [Algebra A K] [FaithfulSMul A K]
    (hinj : Function.Injective (LinearMap.lTensor K f)) :
    Module.Free A C ∧ Module.finrank A C = n := by
  classical
  have hfi : Function.Injective f := by
    intro x y hxy
    have h1 : LinearMap.lTensor K f ((1 : K) ⊗ₜ[A] x) = LinearMap.lTensor K f ((1 : K) ⊗ₜ[A] y) := by
      simp only [LinearMap.lTensor_tmul, hxy]
    have h2 := hinj h1
    funext i
    have h4 := congrArg (fun z => TensorProduct.piScalarRight A K K (Fin n) z i) h2
    simp only [piScalarRight_one_tmul] at h4
    exact FaithfulSMul.algebraMap_injective A K h4
  let e : (Fin n → A) ≃ₗ[A] C := LinearEquiv.ofBijective f ⟨hfi, hf⟩
  exact ⟨Module.Free.of_equiv e, by rw [← e.finrank_eq, Module.finrank_fin_fun]⟩

end FlatCrit

open FlatCrit in

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {C : Type*} [AddCommGroup C] [Module A C] [Module.Finite A C] (n : ℕ)
    (hκ : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] C) = n)
    (hK : Module.finrank (FractionRing A) (FractionRing A ⊗[A] C) = n) :
    Module.Free A C ∧ Module.finrank A C = n := by
  classical
  set κ := IsLocalRing.ResidueField A with hκdef
  set K := FractionRing A with hKdef

  let b : Module.Basis (Fin n) κ (κ ⊗[A] C) := Module.finBasisOfFinrankEq κ (κ ⊗[A] C) hκ
  have hsurj1 : Function.Surjective (TensorProduct.mk A κ C 1) :=
    TensorProduct.mk_surjective A C κ Ideal.Quotient.mk_surjective
  choose g hg using fun i => hsurj1 (b i)
  have hspan : Submodule.span A (Set.range g) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis g b (fun i => hg i)
  let f : (Fin n → A) →ₗ[A] C := Fintype.linearCombination A g
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]

  haveI : Module.Finite K (K ⊗[A] C) := inferInstance
  have hsurjK : Function.Surjective (LinearMap.lTensor K f) := LinearMap.lTensor_surjective K hf
  let fK : (K ⊗[A] (Fin n → A)) →ₗ[K] (K ⊗[A] C) := f.baseChange K
  have hfK : (fK : (K ⊗[A] (Fin n → A)) → (K ⊗[A] C)) = LinearMap.lTensor K f := rfl
  have hsurjK' : Function.Surjective fK := by rw [hfK]; exact hsurjK
  have hdim : Module.finrank K (K ⊗[A] (Fin n → A)) = Module.finrank K (K ⊗[A] C) := by
    rw [Module.finrank_baseChange, Module.finrank_fin_fun, hK]
  haveI : FiniteDimensional K (K ⊗[A] (Fin n → A)) := inferInstance
  have hinjK : Function.Injective fK :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurjK'
  exact free_of_surjective_of_lTensor_injective f hf K (by rw [← hfK]; exact hinjK)

end S_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq
end P2MW
export P2MW.S_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq (solution)
