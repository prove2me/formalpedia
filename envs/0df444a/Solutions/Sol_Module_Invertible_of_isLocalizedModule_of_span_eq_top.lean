-- Prove2me | solution 1 for Module.Invertible.of_isLocalizedModule_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/76490eca-0ecc-5276-a584-35ace2a4b8b1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Invertible_of_isLocalizedModule_of_span_eq_top

set_option autoImplicit false

open TensorProduct

namespace InvLocal29

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (φ : M →ₗ[R] M') [IsLocalizedModule S φ]

include φ in

theorem bijective_map_contractLeft [Module.FinitePresentation R M] [Module.Invertible A M'] :
    Function.Bijective
      (IsLocalizedModule.map S (TensorProduct.mk R A (Module.Dual R M ⊗[R] M) 1) (Algebra.linearMap R A)
        (contractLeft R M)) := by

  let d : Module.Dual R M →ₗ[R] Module.Dual A M' :=
    IsLocalizedModule.mapExtendScalars S φ (Algebra.linearMap R A) A
  haveI : IsLocalizedModule S d :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars S φ (Algebra.linearMap R A) A
  have hd : ∀ (x : Module.Dual R M) (m : M), d x (φ m) = algebraMap R A (x m) := by
    intro x m
    rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply, Algebra.linearMap_apply]
  let eD : A ⊗[R] Module.Dual R M ≃ₗ[A] Module.Dual A M' := (IsLocalizedModule.isBaseChange S A d).equiv
  let eM : A ⊗[R] M ≃ₗ[A] M' := (IsLocalizedModule.isBaseChange S A φ).equiv
  let e : A ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[A] Module.Dual A M' ⊗[A] M' :=
    AlgebraTensorModule.distribBaseChange R A _ _ ≪≫ₗ TensorProduct.congr eD eM
  have key : IsLocalizedModule.map S (TensorProduct.mk R A (Module.Dual R M ⊗[R] M) 1) (Algebra.linearMap R A)
        (contractLeft R M) = ((contractLeft A M') ∘ₗ e.toLinearMap).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S (TensorProduct.mk R A (Module.Dual R M ⊗[R] M) 1)
      (Algebra.linearMap R A)
    rw [IsLocalizedModule.map_comp]
    refine TensorProduct.ext' fun x m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, contractLeft_apply,
      LinearMap.coe_restrictScalars, TensorProduct.mk_apply, LinearEquiv.coe_coe, e, LinearEquiv.trans_apply,
      AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul, eD, eM, IsBaseChange.equiv_tmul,
      one_smul, hd]
  rw [key]
  exact Module.Invertible.bijective.comp e.bijective

end InvLocal29

open InvLocal29 in
theorem solution
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.Invertible (Rₚ g) (Mₚ g)) :
    Module.Invertible R M := by
  have hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := Rₚ) ϕ
      (fun g => by haveI := h g; exact Module.finitePresentation_of_projective (Rₚ g) (Mₚ g))
  refine ⟨bijective_of_isLocalized_span s hs (fun g => Rₚ g ⊗[R] (Module.Dual R M ⊗[R] M))
    (fun g => TensorProduct.mk R (Rₚ g) (Module.Dual R M ⊗[R] M) 1) (fun g => Rₚ g)
    (fun g => Algebra.linearMap R (Rₚ g)) (contractLeft R M) (fun g => ?_)⟩
  haveI := h g
  exact bijective_map_contractLeft (Submonoid.powers g.val) (Rₚ g) (ϕ g)

end S_Module_Invertible_of_isLocalizedModule_of_span_eq_top
end P2MW
export P2MW.S_Module_Invertible_of_isLocalizedModule_of_span_eq_top (solution)
