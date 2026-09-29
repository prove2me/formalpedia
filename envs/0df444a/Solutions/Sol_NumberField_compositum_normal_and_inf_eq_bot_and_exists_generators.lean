-- Prove2me | solution 1 for NumberField.compositum_normal_and_inf_eq_bot_and_exists_generators
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/21ade96c-1235-5c73-9b4b-7f455a927436

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_compositum_normal_and_inf_eq_bot_and_exists_generators

set_option autoImplicit false

theorem solution
    (E F L N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra E F] [Algebra E L] [Algebra E N] [Algebra F N] [Algebra L N]
    [IsScalarTower E F N] [IsScalarTower E L N] [IsGalois E F] [IsGalois E L] [IsGalois E N]
    (hL : IsCyclic (L ≃ₐ[E] L))
    (hdeg : Module.finrank E L = Module.finrank E F)
    (hgen : ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) →
      (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1) :
    ∃ (_ : ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup.Normal)
      (_ : ((IsScalarTower.toAlgHom E L N).fieldRange).fixingSubgroup.Normal),
      ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup ⊓
          ((IsScalarTower.toAlgHom E L N).fieldRange).fixingSubgroup = ⊥ ∧
      Nat.card ((N ≃ₐ[E] N) ⧸ ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup)
          = Nat.card (F ≃ₐ[E] F) ∧
      (∃ s : (N ≃ₐ[E] N) ⧸ ((IsScalarTower.toAlgHom E L N).fieldRange).fixingSubgroup,
        (∀ g, g ∈ Subgroup.zpowers s) ∧
        orderOf s = Nat.card ((N ≃ₐ[E] N) ⧸ ((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup)) ∧
      (∃ t : ↥((IsScalarTower.toAlgHom E F N).fieldRange).fixingSubgroup,
        ∀ g, g ∈ Subgroup.zpowers t) := by
  classical

  let Γ := N ≃ₐ[E] N
  let KF : IntermediateField E N := (IsScalarTower.toAlgHom E F N).fieldRange
  let KL : IntermediateField E N := (IsScalarTower.toAlgHom E L N).fieldRange
  let rF : (N ≃ₐ[E] N) →* (F ≃ₐ[E] F) := AlgEquiv.restrictNormalHom F
  let rL : (N ≃ₐ[E] N) →* (L ≃ₐ[E] L) := AlgEquiv.restrictNormalHom L

  have memF : ∀ σ : N ≃ₐ[E] N, σ ∈ KF.fixingSubgroup ↔ ∀ x : F, σ (algebraMap F N x) = algebraMap F N x := by
    intro σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    · rintro h _ hy
      obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
      exact h x
  have memL : ∀ σ : N ≃ₐ[E] N, σ ∈ KL.fixingSubgroup ↔ ∀ y : L, σ (algebraMap L N y) = algebraMap L N y := by
    intro σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y
      exact h _ (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
    · rintro h _ hy
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hy
      exact h y

  have kerF : KF.fixingSubgroup = rF.ker := by
    ext σ
    rw [memF, MonoidHom.mem_ker]
    constructor
    · intro h
      apply AlgEquiv.ext
      intro x
      apply (algebraMap F N).injective
      show algebraMap F N (σ.restrictNormal F x) = algebraMap F N x
      rw [AlgEquiv.restrictNormal_commutes, h x]
    · intro h x
      have hx := AlgEquiv.restrictNormal_commutes σ F x
      have h' : σ.restrictNormal F = 1 := h
      rw [h', AlgEquiv.one_apply] at hx
      exact hx.symm
  have kerL : KL.fixingSubgroup = rL.ker := by
    ext σ
    rw [memL, MonoidHom.mem_ker]
    constructor
    · intro h
      apply AlgEquiv.ext
      intro y
      apply (algebraMap L N).injective
      show algebraMap L N (σ.restrictNormal L y) = algebraMap L N y
      rw [AlgEquiv.restrictNormal_commutes, h y]
    · intro h y
      have hy := AlgEquiv.restrictNormal_commutes σ L y
      have h' : σ.restrictNormal L = 1 := h
      rw [h', AlgEquiv.one_apply] at hy
      exact hy.symm
  have surjF : Function.Surjective rF := AlgEquiv.restrictNormalHom_surjective N
  have surjL : Function.Surjective rL := AlgEquiv.restrictNormalHom_surjective N

  haveI nF : KF.fixingSubgroup.Normal := by rw [kerF]; infer_instance
  haveI nL : KL.fixingSubgroup.Normal := by rw [kerL]; infer_instance

  have eF : (N ≃ₐ[E] N) ⧸ KF.fixingSubgroup ≃* (F ≃ₐ[E] F) :=
    (QuotientGroup.quotientMulEquivOfEq kerF).trans (QuotientGroup.quotientKerEquivOfSurjective rF surjF)
  have eL : (N ≃ₐ[E] N) ⧸ KL.fixingSubgroup ≃* (L ≃ₐ[E] L) :=
    (QuotientGroup.quotientMulEquivOfEq kerL).trans (QuotientGroup.quotientKerEquivOfSurjective rL surjL)

  have hinf : KF.fixingSubgroup ⊓ KL.fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    exact hgen σ ((memF σ).mp hσ.1) ((memL σ).mp hσ.2)
  have cardF : Nat.card (F ≃ₐ[E] F) = Module.finrank E F := IsGalois.card_aut_eq_finrank E F
  have cardL : Nat.card (L ≃ₐ[E] L) = Module.finrank E L := IsGalois.card_aut_eq_finrank E L
  refine ⟨nF, nL, hinf, ?_, ?_, ?_⟩
  · exact (Nat.card_congr eF.toEquiv)
  ·
    haveI : IsCyclic ((N ≃ₐ[E] N) ⧸ KL.fixingSubgroup) := isCyclic_of_surjective eL.symm eL.symm.surjective
    obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := (N ≃ₐ[E] N) ⧸ KL.fixingSubgroup)
    refine ⟨s, hs, ?_⟩
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_congr eL.toEquiv, Nat.card_congr eF.toEquiv,
      cardL, cardF, hdeg]
  ·
    haveI : IsCyclic ((N ≃ₐ[E] N) ⧸ KL.fixingSubgroup) := isCyclic_of_surjective eL.symm eL.symm.surjective
    have hinjS : Function.Injective ((QuotientGroup.mk' KL.fixingSubgroup).comp KF.fixingSubgroup.subtype) := by
      intro a b h
      apply Subtype.ext
      have h' : (QuotientGroup.mk' KL.fixingSubgroup) (a : N ≃ₐ[E] N) = (QuotientGroup.mk' KL.fixingSubgroup) b := h
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
      have hmem : (a : N ≃ₐ[E] N)⁻¹ * b ∈ KF.fixingSubgroup ⊓ KL.fixingSubgroup :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2, h'⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact inv_mul_eq_one.mp hmem
    haveI : IsCyclic ↥KF.fixingSubgroup := isCyclic_of_injective _ hinjS
    exact IsCyclic.exists_generator

end S_NumberField_compositum_normal_and_inf_eq_bot_and_exists_generators
end P2MW
export P2MW.S_NumberField_compositum_normal_and_inf_eq_bot_and_exists_generators (solution)
