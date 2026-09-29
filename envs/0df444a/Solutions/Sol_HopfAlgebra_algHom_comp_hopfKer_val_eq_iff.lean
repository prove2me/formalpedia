-- Prove2me | solution 1 for HopfAlgebra.algHom_comp_hopfKer_val_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c39a712e-bcae-5d9e-938f-c3d02f2a1f00

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct
open HopfAlgebra

universe u v w x

namespace S17KT5d

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
variable {k : Type x} [CommRing k] [Algebra R k]
variable (π : A →ₐc[R] B)

noncomputable def act (ψ : A →ₐ[R] k) (χ : B →ₐ[R] k) : A →ₐ[R] k :=
  (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (coaction π)

theorem act_apply (ψ : A →ₐ[R] k) (χ : B →ₐ[R] k) (a : A) :
    act π ψ χ a = Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _) (coaction π a) := rfl

theorem act_apply_of_mem (ψ : A →ₐ[R] k) (χ : B →ₐ[R] k) {h : A} (hh : h ∈ hopfKer π) :
    act π ψ χ h = ψ h := by
  rw [act_apply, coaction_eq_of_mem π hh, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

noncomputable def res (ψ : A →ₐ[R] k) : ↥(hopfKer π) →ₐ[R] k := ψ.comp (hopfKer π).val

theorem res_act (ψ : A →ₐ[R] k) (χ : B →ₐ[R] k) : res π (act π ψ χ) = res π ψ := by
  apply AlgHom.ext; intro h
  exact act_apply_of_mem π ψ χ h.2

theorem lift_comp_canAlgHom (ψ : A →ₐ[R] k) (χ : B →ₐ[R] k) :
    (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (canAlgHom π) =
      Algebra.TensorProduct.lift ψ (act π ψ χ) (fun _ _ => Commute.all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro a a'
  rw [AlgHom.comp_apply, canAlgHom_tmul, map_mul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
    map_one, mul_one, act_apply]

theorem act_injective (hsurj : Function.Surjective (canMap π)) (ψ : A →ₐ[R] k) :
    Function.Injective (act π ψ) := by
  intro χ χ' h
  have hl : Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.lift ψ χ' (fun _ _ => Commute.all _ _) := by
    apply AlgHom.ext; intro z
    obtain ⟨y, rfl⟩ := hsurj z
    have e1 := congrArg (fun F : A ⊗[R] A →ₐ[R] k => F y) (lift_comp_canAlgHom π ψ χ)
    have e2 := congrArg (fun F : A ⊗[R] A →ₐ[R] k => F y) (lift_comp_canAlgHom π ψ χ')
    simp only [AlgHom.comp_apply] at e1 e2
    rw [canMap_apply, e1, e2, h]
  apply AlgHom.ext; intro b
  have := congrArg (fun F : A ⊗[R] B →ₐ[R] k => F (1 ⊗ₜ[R] b)) hl
  simpa [Algebra.TensorProduct.lift_tmul] using this

theorem exists_act_eq (hHG : IsHopfGalois π) (ψ ψ' : A →ₐ[R] k) (hres : res π ψ = res π ψ') :
    ∃ χ : B →ₐ[R] k, act π ψ χ = ψ' := by

  let Θ : A ⊗[R] A →ₐ[R] k := Algebra.TensorProduct.lift ψ ψ' (fun _ _ => Commute.all _ _)
  have hΘ : ∀ z, canAlgHom π z = 0 → Θ z = 0 := by
    intro z hz
    have hz' : z ∈ Submodule.span R (balancingRelations π) := hHG.2 z hz
    have key : ∀ x ∈ balancingRelations π, Θ x = 0 := by
      rintro x ⟨a, h, a', hh, rfl⟩
      have e : ψ h = ψ' h := by
        have := congrArg (fun F : ↥(hopfKer π) →ₐ[R] k => F ⟨h, hh⟩) hres
        exact this
      simp only [Θ, map_sub, Algebra.TensorProduct.lift_tmul, map_mul, e]
      ring

    have hle : Submodule.span R (balancingRelations π) ≤ LinearMap.ker Θ.toLinearMap :=
      Submodule.span_le.mpr fun x hx => key x hx
    exact hle hz'

  have hker : ∀ z ∈ RingHom.ker (canAlgHom π).toRingHom, Θ z = 0 := fun z hz => hΘ z hz
  let e : (A ⊗[R] A ⧸ RingHom.ker (canAlgHom π).toRingHom) ≃ₐ[R] A ⊗[R] B :=
    Ideal.quotientKerAlgEquivOfSurjective hHG.1
  let θ : A ⊗[R] B →ₐ[R] k := (Ideal.Quotient.liftₐ _ Θ hker).comp e.symm.toAlgHom
  have hθ : ∀ z, θ (canAlgHom π z) = Θ z := by
    intro z
    have h1 : e.symm (canAlgHom π z) = Ideal.Quotient.mk _ z := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    show (Ideal.Quotient.liftₐ _ Θ hker) (e.symm (canAlgHom π z)) = Θ z
    rw [h1]
    rfl

  let χ : B →ₐ[R] k := θ.comp Algebra.TensorProduct.includeRight
  have hθL : ∀ a, θ (a ⊗ₜ[R] 1) = ψ a := by
    intro a
    rw [← canMap_tmul_one π a, canMap_apply, hθ]
    simp only [Θ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hθ' : θ = Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [Algebra.TensorProduct.lift_tmul]
    have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul, hθL]
    rfl
  refine ⟨χ, ?_⟩
  apply AlgHom.ext; intro a'
  rw [act_apply, ← hθ', ← canMap_one_tmul, canMap_apply, hθ]
  simp only [Θ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end S17KT5d

open S17KT5d in
theorem solution {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : HopfAlgebra.IsHopfGalois π)
    {k : Type x} [CommRing k] [Algebra R k] (ψ ψ' : A →ₐ[R] k) :
    ψ.comp (HopfAlgebra.hopfKer π).val = ψ'.comp (HopfAlgebra.hopfKer π).val
      ↔ ∃! χ : B →ₐ[R] k,
          (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (HopfAlgebra.coaction π) = ψ' := by
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := exists_act_eq π hπ ψ ψ' h
    exact ⟨χ, hχ, fun χ' hχ' => act_injective π hπ.1 ψ (hχ'.trans hχ.symm)⟩
  · rintro ⟨χ, hχ, -⟩
    rw [← hχ]
    exact (res_act π ψ χ).symm

end S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff
end P2MW
export P2MW.S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff (solution)
