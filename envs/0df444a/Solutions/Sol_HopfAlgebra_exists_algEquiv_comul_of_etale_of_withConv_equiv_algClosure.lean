-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9c67fc9a-c64a-5fbf-892d-978777b55577

import Mathlib
import Theorems.Thm_Algebra_Etale_existsUnique_algHom_forall_comp_eq_of_equivariant
import Theorems.Thm_Algebra_Etale_algHom_ext_of_forall_comp_eq
import Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure

set_option maxHeartbeats 16000000
open scoped TensorProduct

theorem solution
    (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {M : Type*} [AddCommGroup M] [DistribMulAction (Ω ≃ₐ[K] Ω) M]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.Etale K A]
    (eA : WithConv (A →ₐ[K] Ω) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (A →ₐ[K] Ω)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type*) [CommRing B] [HopfAlgebra K B] [Algebra.Etale K B]
    (eB : WithConv (B →ₐ[K] Ω) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (B →ₐ[K] Ω)),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f)) :
    ∃ φ : B ≃ₐ[K] A,
      ∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x) := by
  classical

  have heBs_act : ∀ (σ : Ω ≃ₐ[K] Ω) (m : M),
      (eB.symm (σ • m)).ofConv = σ.toAlgHom.comp (eB.symm m).ofConv := by
    intro σ m
    have key : eB (WithConv.toConv (σ.toAlgHom.comp (eB.symm m).ofConv)) = σ • m := by
      have h := heB_act σ (eB.symm m) (WithConv.toConv (σ.toAlgHom.comp (eB.symm m).ofConv))
        (fun b => rfl)
      simpa only [Equiv.apply_symm_apply] using h
    rw [← key, Equiv.symm_apply_apply, WithConv.ofConv_toConv]
  have heAs_act : ∀ (σ : Ω ≃ₐ[K] Ω) (m : M),
      (eA.symm (σ • m)).ofConv = σ.toAlgHom.comp (eA.symm m).ofConv := by
    intro σ m
    have key : eA (WithConv.toConv (σ.toAlgHom.comp (eA.symm m).ofConv)) = σ • m := by
      have h := heA_act σ (eA.symm m) (WithConv.toConv (σ.toAlgHom.comp (eA.symm m).ofConv))
        (fun a => rfl)
      simpa only [Equiv.apply_symm_apply] using h
    rw [← key, Equiv.symm_apply_apply, WithConv.ofConv_toConv]

  let Φ : (A →ₐ[K] Ω) → (B →ₐ[K] Ω) := fun χ => (eB.symm (eA (WithConv.toConv χ))).ofConv
  have hΦeq : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : A →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ) := by
    intro γ χ
    have h1 : eA (WithConv.toConv (γ.toAlgHom.comp χ)) = γ • eA (WithConv.toConv χ) :=
      heA_act γ (WithConv.toConv χ) (WithConv.toConv (γ.toAlgHom.comp χ)) (fun a => rfl)
    show (eB.symm (eA (WithConv.toConv (γ.toAlgHom.comp χ)))).ofConv
       = γ.toAlgHom.comp (eB.symm (eA (WithConv.toConv χ))).ofConv
    rw [h1, heBs_act]
  obtain ⟨ψ, hψ, hψuniq⟩ :=
    Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant (B := B) (C := A) Φ hΦeq

  let Φ' : (B →ₐ[K] Ω) → (A →ₐ[K] Ω) := fun χ => (eA.symm (eB (WithConv.toConv χ))).ofConv
  have hΦ'eq : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : B →ₐ[K] Ω),
      Φ' (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ' χ) := by
    intro γ χ
    have h1 : eB (WithConv.toConv (γ.toAlgHom.comp χ)) = γ • eB (WithConv.toConv χ) :=
      heB_act γ (WithConv.toConv χ) (WithConv.toConv (γ.toAlgHom.comp χ)) (fun b => rfl)
    show (eA.symm (eB (WithConv.toConv (γ.toAlgHom.comp χ)))).ofConv
       = γ.toAlgHom.comp (eA.symm (eB (WithConv.toConv χ))).ofConv
    rw [h1, heAs_act]
  obtain ⟨ψ', hψ', _⟩ :=
    Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant (B := A) (C := B) Φ' hΦ'eq

  have hΦΦ' : ∀ χ, Φ' (Φ χ) = χ := fun χ => by
    simp only [Φ, Φ', WithConv.toConv_ofConv, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
               WithConv.ofConv_toConv]
  have hΦ'Φ : ∀ χ, Φ (Φ' χ) = χ := fun χ => by
    simp only [Φ, Φ', WithConv.toConv_ofConv, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
               WithConv.ofConv_toConv]

  have hψψ' : ψ.comp ψ' = AlgHom.id K A := by
    refine Algebra.Etale.algHom_ext_of_forall_comp_eq (Ω := Ω) (fun χ => ?_)
    rw [← AlgHom.comp_assoc, hψ, hψ' (Φ χ), hΦΦ', AlgHom.comp_id]
  have hψ'ψ : ψ'.comp ψ = AlgHom.id K B := by
    refine Algebra.Etale.algHom_ext_of_forall_comp_eq (Ω := Ω) (fun χ => ?_)
    rw [← AlgHom.comp_assoc, hψ', hψ (Φ' χ), hΦ'Φ, AlgHom.comp_id]

  refine ⟨AlgEquiv.ofAlgHom ψ ψ' hψψ' hψ'ψ, fun x => ?_⟩

  show CoalgebraStruct.comul (R := K) (ψ x)
    = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (CoalgebraStruct.comul (R := K) x)

  have P1A : ∀ (ρ₁ ρ₂ : A →ₐ[K] Ω) (y : A),
      (WithConv.toConv ρ₁ * WithConv.toConv ρ₂).ofConv y
        = (Algebra.TensorProduct.lift ρ₁ ρ₂ (fun _ _ => mul_comm _ _))
            (Coalgebra.comul (R := K) y) := by
    intro ρ₁ ρ₂ y
    show LinearMap.mul' K Ω
        (TensorProduct.map ρ₁.toLinearMap ρ₂.toLinearMap (Coalgebra.comul (R := K) y)) = _
    induction Coalgebra.comul (R := K) y using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
                 Algebra.TensorProduct.lift_tmul]
    | add p q hp hq => simp only [map_add, hp, hq]
  have P1B : ∀ (ρ₁ ρ₂ : B →ₐ[K] Ω) (y : B),
      (WithConv.toConv ρ₁ * WithConv.toConv ρ₂).ofConv y
        = (Algebra.TensorProduct.lift ρ₁ ρ₂ (fun _ _ => mul_comm _ _))
            (Coalgebra.comul (R := K) y) := by
    intro ρ₁ ρ₂ y
    show LinearMap.mul' K Ω
        (TensorProduct.map ρ₁.toLinearMap ρ₂.toLinearMap (Coalgebra.comul (R := K) y)) = _
    induction Coalgebra.comul (R := K) y using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
                 Algebra.TensorProduct.lift_tmul]
    | add p q hp hq => simp only [map_add, hp, hq]
  haveI : Algebra.Etale A (A ⊗[K] A) := Algebra.Etale.baseChange K A A
  haveI : Algebra.Etale K (A ⊗[K] A) := Algebra.Etale.comp K A (A ⊗[K] A)
  refine Algebra.Etale.eq_of_forall_algHom_apply_eq (K := K) (Ω := Ω) (B := A ⊗[K] A)
    (fun θ => ?_)
  set χ₁ := θ.comp Algebra.TensorProduct.includeLeft with hχ₁
  set χ₂ := θ.comp Algebra.TensorProduct.includeRight with hχ₂
  have hθ : θ = Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => mul_comm _ _) := by
    refine Algebra.TensorProduct.ext ?_ ?_
    · ext a; simp [hχ₁, Algebra.TensorProduct.lift_tmul]
    · ext a; simp [hχ₂, Algebra.TensorProduct.lift_tmul]
  have hLHS : θ (CoalgebraStruct.comul (R := K) (ψ x))
      = (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv (ψ x) := by
    rw [hθ, P1A χ₁ χ₂ (ψ x)]
  have hRHS : θ ((TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (CoalgebraStruct.comul (R := K) x))
      = (WithConv.toConv (χ₁.comp ψ) * WithConv.toConv (χ₂.comp ψ)).ofConv x := by
    rw [P1B (χ₁.comp ψ) (χ₂.comp ψ) x, hθ]
    have hmap : ∀ z : B ⊗[K] B,
        (Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => mul_comm _ _))
            ((Algebra.TensorProduct.map ψ ψ) z)
        = (Algebra.TensorProduct.lift (χ₁.comp ψ) (χ₂.comp ψ) (fun _ _ => mul_comm _ _)) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
                   AlgHom.comp_apply]
      | add p q hp hq => simp only [map_add, hp, hq]
    have hP3 : ∀ z : B ⊗[K] B,
        (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) z
          = (Algebra.TensorProduct.map ψ ψ) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ => simp [Algebra.TensorProduct.map_tmul]
      | add p q hp hq => simp only [map_add, hp, hq]
    rw [hP3, hmap]
  rw [hLHS, hRHS]
  rw [show (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv (ψ x)
      = ((WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv.comp ψ) x from rfl]
  rw [hψ ((WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv), hψ χ₁, hψ χ₂]
  show (eB.symm (eA (WithConv.toConv (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv))).ofConv x
    = (WithConv.toConv (eB.symm (eA (WithConv.toConv χ₁))).ofConv
      * WithConv.toConv (eB.symm (eA (WithConv.toConv χ₂))).ofConv).ofConv x
  rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv, WithConv.toConv_ofConv]
  have key : eB.symm (eA (WithConv.toConv χ₁ * WithConv.toConv χ₂))
      = eB.symm (eA (WithConv.toConv χ₁)) * eB.symm (eA (WithConv.toConv χ₂)) := by
    apply eB.injective
    rw [Equiv.apply_symm_apply, heB_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, heA_add]
  rw [key]

end S_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure (solution)
