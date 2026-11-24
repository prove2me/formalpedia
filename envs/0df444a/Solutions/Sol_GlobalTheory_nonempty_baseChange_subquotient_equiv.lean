-- Prove2me | solution 1 for GlobalTheory.nonempty_baseChange_subquotient_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:59.607852+00:00
-- url     : https://prove2.me/submissions/6275abd8-3b4c-4c2a-89f6-7c85601d0feb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution [Module.Flat R S] {X : Type*} [AddCommGroup X]
    [Module R X] (A B : Submodule R X) :
    Nonempty ((S ⊗[R] (A ⧸ B.submoduleOf A)) ≃ₗ[S]
      (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S))) := by
  let h : S ⊗[R] A →ₗ[S] S ⊗[R] (A ⧸ B.submoduleOf A) := (B.submoduleOf A).mkQ.baseChange S
  let g : S ⊗[R] A →ₗ[S] (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) :=
    ((B.baseChange S).submoduleOf (A.baseChange S)).mkQ ∘ₗ A.toBaseChange S
  have hh : Function.Surjective h :=
    LinearMap.lTensor_surjective S (B.submoduleOf A).mkQ_surjective
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (A.toBaseChange_surjective S)
  have e₁ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.submoduleOf A).mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have e₂ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.mkQ ∘ₗ A.subtype).lTensor S) := by
    apply Module.Flat.lTensor_exact S
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
    rfl
  have e₃ : Function.Exact (B.subtype.lTensor S) (B.mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have hker : LinearMap.ker h = LinearMap.ker g := by
    ext x
    have h1 : x ∈ LinearMap.ker h ↔ (B.submoduleOf A).mkQ.lTensor S x = 0 := Iff.rfl
    have h2 : x ∈ LinearMap.ker g ↔ A.subtype.lTensor S x ∈ B.baseChange S := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h1, h2, e₁ x, ← e₂ x, LinearMap.lTensor_comp, LinearMap.comp_apply, e₃]
    rfl
  exact ⟨(h.quotKerEquivOfSurjective hh).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    g.quotKerEquivOfSurjective hg⟩
end GlobalTheory
