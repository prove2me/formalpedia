-- Prove2me | solution 1 for HeckeCohomology.commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fb9b7b2b-f07d-507f-b054-81a4d990b0e1

import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Theorems.Thm_HeckeCohomology_heckeH1_eq_of_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid

set_option autoImplicit false

open groupCohomology HeckeCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace DiamondH1

section Inner
variable {k Γ : Type} [CommRing k] [Group Γ] (A : Rep k Γ)

scoped instance subsingleton_quotient_rightRel_top : Subsingleton (Quotient (QuotientGroup.rightRel (⊤ : Subgroup Γ))) :=
  ⟨fun a b => Quotient.inductionOn₂' a b fun x y => Quotient.sound' (by
    rw [QuotientGroup.rightRel_apply]; exact Subgroup.mem_top _)⟩

theorem rho_inv_rho (g₀ : Γ) (w : A) : A.ρ g₀⁻¹ (A.ρ g₀ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_inv_rho_conj (g₀ γ : Γ) (w : A) : A.ρ g₀⁻¹ (A.ρ (g₀ * γ * g₀⁻¹) w) = A.ρ γ (A.ρ g₀⁻¹ w) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem conj_identity (f : cocycles₁ A) (g₀ γ : Γ) :
    A.ρ g₀⁻¹ (f (g₀ * γ * g₀⁻¹)) = f γ - (A.ρ γ (A.ρ g₀⁻¹ (f g₀)) - A.ρ g₀⁻¹ (f g₀)) := by
  have hc := (mem_cocycles₁_iff f).1 f.2
  have e1 : f (g₀ * γ) = A.ρ g₀ (f γ) + f g₀ := hc g₀ γ
  have e2 : f (g₀ * γ * g₀⁻¹ * g₀) = A.ρ (g₀ * γ * g₀⁻¹) (f g₀) + f (g₀ * γ * g₀⁻¹) := hc _ _
  rw [inv_mul_cancel_right, e1] at e2
  have e3 : f (g₀ * γ * g₀⁻¹) = A.ρ g₀ (f γ) + f g₀ - A.ρ (g₀ * γ * g₀⁻¹) (f g₀) :=
    eq_sub_of_add_eq' e2.symm
  rw [e3, map_sub, map_add, rho_inv_rho, rho_inv_rho_conj]
  abel

theorem H1π_inner_eq (f g : cocycles₁ A) (g₀ : Γ) (hg : ∀ γ, g γ = A.ρ g₀⁻¹ (f (g₀ * γ * g₀⁻¹))) :
    H1π A g = H1π A f := by
  rw [H1π_eq_iff]
  refine ⟨-(A.ρ g₀⁻¹ (f g₀)), funext fun γ => ?_⟩
  show A.ρ γ (-(A.ρ g₀⁻¹ (f g₀))) - -(A.ρ g₀⁻¹ (f g₀)) = _
  rw [Pi.sub_apply, hg, conj_identity A f g₀ γ, map_neg]
  abel

end Inner

section Auto

variable {k Γ : Type} [CommRing k] [Group Γ] (A : Rep k Γ)
variable (θ : Γ →* Γ) (ψ : A →ₗ[k] A)

def autoZ (hψ : ∀ (s : Γ) (a : A), ψ (A.ρ (θ s) a) = A.ρ s (ψ a)) (f : cocycles₁ A) : cocycles₁ A :=
  ⟨fun γ => ψ (f (θ γ)), by
    rw [mem_cocycles₁_iff]
    intro g h
    rw [map_mul, (mem_cocycles₁_iff f).1 f.2, map_add, hψ]⟩

theorem autoZ_apply (hψ : ∀ (s : Γ) (a : A), ψ (A.ρ (θ s) a) = A.ρ s (ψ a)) (f : cocycles₁ A) (γ : Γ) :
    autoZ A θ ψ hψ f γ = ψ (f (θ γ)) := rfl

theorem heckeH1_top_eq (hψt : IsTwist ⊤ ⊤ ((θ.comp (⊤ : Subgroup Γ).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _) A ψ)
    (f : cocycles₁ A) :
    heckeH1 ⊤ ⊤ ((θ.comp (⊤ : Subgroup Γ).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _) A ψ hψt (H1π A f) =
      H1π A (autoZ A θ ψ (fun s a => hψt ⟨s, Subgroup.mem_top s⟩ a) f) := by
  symm
  refine HeckeCohomology.heckeH1_eq_of_section ⊤ ⊤ _ A ψ hψt (fun _ => 1) (fun _ γ => ⟨γ, Subgroup.mem_top γ⟩)
    (fun q γ => by simp) f _ (fun γ => ?_)
  rw [Fintype.sum_subsingleton _ (cls (⊤ : Subgroup Γ) 1), autoZ_apply, inv_one, map_one, Module.End.one_apply]
  rfl

end Auto

section Gamma

variable (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)

def mInv (σ : CongruenceSubgroup.Gamma0 N) : M :=
  ⟨(((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹).2⟩

theorem mInv_mul (σ τ : CongruenceSubgroup.Gamma0 N) : mInv N M hΓ σ * mInv N M hΓ τ = mInv N M hΓ (τ * σ) := by
  apply Subtype.ext
  show (((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((τ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    ((((τ * σ)⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [mul_inv_rev, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem comm_mem (σ τ : CongruenceSubgroup.Gamma0 N) :
    (((τ * σ)⁻¹ * (σ * τ) : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CohCarrier.GammaH N ⊥ := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨((τ * σ)⁻¹ * (σ * τ)).2, ?_⟩

  rw [Subgroup.mem_bot]
  have : (⟨(((τ * σ)⁻¹ * (σ * τ) : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ), ((τ * σ)⁻¹ * (σ * τ)).2⟩ :
      CongruenceSubgroup.Gamma0 N) = (τ * σ)⁻¹ * (σ * τ) := rfl
  rw [this, map_mul, map_inv, map_mul, map_mul, mul_comm (CohCarrier.gamma0Units N τ), inv_mul_cancel]

end Gamma

end DiamondH1
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.DiamondH1"

open DiamondH1 in
theorem solution
    (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)
    (σ : CongruenceSubgroup.Gamma0 N)
    (hψ : HeckeCohomology.IsTwist ⊤ ⊤
            (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
            X (ρ' ⟨(((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹).2⟩))
    (τ : CongruenceSubgroup.Gamma0 N)
    (hψ' : HeckeCohomology.IsTwist ⊤ ⊤
            (((CohCarrier.conjHom N ⊥ τ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
            X (ρ' ⟨(((τ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (τ⁻¹).2⟩)) :
    Commute
      (HeckeCohomology.heckeH1 ⊤ ⊤
          (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
          X _ hψ)
      (HeckeCohomology.heckeH1 ⊤ ⊤
          (((CohCarrier.conjHom N ⊥ τ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
          X _ hψ') := by
  classical

  set θσ : ↥(CohCarrier.GammaH N ⊥) →* ↥(CohCarrier.GammaH N ⊥) := CohCarrier.conjHom N ⊥ σ with hθσ
  set θτ : ↥(CohCarrier.GammaH N ⊥) →* ↥(CohCarrier.GammaH N ⊥) := CohCarrier.conjHom N ⊥ τ with hθτ
  have hψ₁ : ∀ (s : ↥(CohCarrier.GammaH N ⊥)) (a : X), ρ' (mInv N M hΓ σ) (X.ρ (θσ s) a) = X.ρ s (ρ' (mInv N M hΓ σ) a) :=
    fun s a => hψ ⟨s, Subgroup.mem_top s⟩ a
  have hψ₂ : ∀ (s : ↥(CohCarrier.GammaH N ⊥)) (a : X), ρ' (mInv N M hΓ τ) (X.ρ (θτ s) a) = X.ρ s (ρ' (mInv N M hΓ τ) a) :=
    fun s a => hψ' ⟨s, Subgroup.mem_top s⟩ a

  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := H1π_surjective X x
  show heckeH1 ⊤ ⊤ _ X _ hψ (heckeH1 ⊤ ⊤ _ X _ hψ' (H1π X f)) = heckeH1 ⊤ ⊤ _ X _ hψ' (heckeH1 ⊤ ⊤ _ X _ hψ (H1π X f))
  rw [heckeH1_top_eq X θτ _ hψ' f, heckeH1_top_eq X θσ _ hψ, heckeH1_top_eq X θσ _ hψ f, heckeH1_top_eq X θτ _ hψ']

  set c : ↥(CohCarrier.GammaH N ⊥) := ⟨(((σ * τ)⁻¹ * (τ * σ) : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ),
    comm_mem N τ σ⟩ with hc

  set gστ := autoZ X θσ (ρ' (mInv N M hΓ σ)) hψ₁ (autoZ X θτ (ρ' (mInv N M hΓ τ)) hψ₂ f) with hgστ
  set gτσ := autoZ X θτ (ρ' (mInv N M hΓ τ)) hψ₂ (autoZ X θσ (ρ' (mInv N M hΓ σ)) hψ₁ f) with hgτσ

  refine H1π_inner_eq X gτσ gστ c fun γ => ?_
  have hc' : ((c : ↥(CohCarrier.GammaH N ⊥)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      ((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * τ)⁻¹ * (τ * σ) := rfl

  have hgrp : θσ (θτ (c * γ * c⁻¹)) = θτ (θσ γ) := by
    apply Subtype.ext
    show (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) *
        ((τ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * ((c * γ * c⁻¹ : ↥(CohCarrier.GammaH N ⊥)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) *
          (τ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹) * (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ =
      (τ : Matrix.SpecialLinearGroup (Fin 2) ℤ) *
        ((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹) *
          (τ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc']
    group

  have hcoef : ∀ v : X, X.ρ c⁻¹ (ρ' (mInv N M hΓ τ) (ρ' (mInv N M hΓ σ) v)) = ρ' (mInv N M hΓ σ) (ρ' (mInv N M hΓ τ) v) := by
    intro v
    rw [hρ' c⁻¹, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply (ρ' _) (ρ' _), ← map_mul]
    congr 2
    apply Subtype.ext
    show (((c⁻¹ : ↥(CohCarrier.GammaH N ⊥)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((τ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((τ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1
    rw [Subgroup.coe_inv, hc', Subgroup.coe_inv, Subgroup.coe_inv]
    group
  simp only [hgστ, hgτσ, autoZ_apply]
  rw [hgrp, hcoef]

end S_HeckeCohomology_commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
end P2MW
export P2MW.S_HeckeCohomology_commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid (solution)
