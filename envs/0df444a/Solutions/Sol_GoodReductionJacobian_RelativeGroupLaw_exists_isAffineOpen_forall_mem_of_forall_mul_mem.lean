-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/05747540-b79c-5a15-b726-d5511cd6844c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TranslateCoverAux

variable {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)

theorem mul_coe_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (e : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ g) (P₂ Q₂ : SchemeHomOver t₂ g) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (LB.mul t₁ P₁ Q₁).1 = (LB.mul t₂ P₂ Q₂).1 := by
  subst e
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    schemeHomOverComp ψ hψ (LB.inv t x) = LB.inv t' (schemeHomOverComp ψ hψ x) := by
  have h : LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x)) (schemeHomOverComp ψ hψ x) = LB.one t' := by
    rw [← LB.mul_natural, LB.inv_mul_cancel, LB.one_natural]
  calc schemeHomOverComp ψ hψ (LB.inv t x)
      = LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x)) (LB.one t') := (LB.mul_one t' _).symm
    _ = LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x))
          (LB.mul t' (schemeHomOverComp ψ hψ x) (LB.inv t' (schemeHomOverComp ψ hψ x))) := by
        rw [LB.mul_inv_cancel]
    _ = LB.mul t' (LB.one t') (LB.inv t' (schemeHomOverComp ψ hψ x)) := by rw [← LB.mul_assoc, h]
    _ = LB.inv t' (schemeHomOverComp ψ hψ x) := LB.one_mul t' _

end TranslateCoverAux

theorem solution
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of R))
    [IsFinite t₁] [Flat t₁] [LocallyOfFinitePresentation t₁] [Surjective t₁]
    (γ : SchemeHomOver t₁ g) (U : B.Opens) (hU : IsAffineOpen U) (S : Finset B)
    (hS : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B) (t : Spec (CommRingCat.of K) ⟶ T)
      (hx : x ≫ g = t ≫ t₁), x.base (IsLocalRing.closedPoint K) ∈ S →
      (LB.mul (t ≫ t₁) (schemeHomOverComp t rfl γ) ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by
  classical

  let p : pullback g t₁ ⟶ B := pullback.fst g t₁
  let q : pullback g t₁ ⟶ T := pullback.snd g t₁
  have hpq : p ≫ g = q ≫ t₁ := pullback.condition

  let P₀ : SchemeHomOver (p ≫ g) g := ⟨p, rfl⟩
  let γq : SchemeHomOver (p ≫ g) g := schemeHomOverComp q hpq.symm γ

  let lam : pullback g t₁ ⟶ pullback g t₁ :=
    pullback.lift (LB.mul (p ≫ g) γq P₀).1 q (by rw [(LB.mul (p ≫ g) γq P₀).2, hpq])
  let lam' : pullback g t₁ ⟶ pullback g t₁ :=
    pullback.lift (LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).1 q
      (by rw [(LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).2, hpq])
  have lam_fst : lam ≫ p = (LB.mul (p ≫ g) γq P₀).1 := pullback.lift_fst _ _ _
  have lam_snd : lam ≫ q = q := pullback.lift_snd _ _ _
  have lam'_fst : lam' ≫ p = (LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).1 := pullback.lift_fst _ _ _
  have lam'_snd : lam' ≫ q = q := pullback.lift_snd _ _ _
  have hlam : lam ≫ (p ≫ g) = p ≫ g := by rw [← Category.assoc, lam_fst, (LB.mul (p ≫ g) γq P₀).2]
  have hlam' : lam' ≫ (p ≫ g) = p ≫ g := by
    rw [← Category.assoc, lam'_fst, (LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).2]

  have comp_γq : ∀ (μ : pullback g t₁ ⟶ pullback g t₁) (hμ : μ ≫ (p ≫ g) = p ≫ g) (hq : μ ≫ q = q),
      schemeHomOverComp μ hμ γq = γq := by
    intro μ hμ hq
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, γq, ← Category.assoc, hq]
  have comp_P₀ : ∀ (μ : pullback g t₁ ⟶ pullback g t₁) (hμ : μ ≫ (p ≫ g) = p ≫ g),
      (schemeHomOverComp μ hμ P₀).1 = μ ≫ p := fun _ _ => rfl
  have h1 : lam ≫ lam' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      change lam ≫ lam' ≫ p = p
      rw [lam'_fst]
      have := congrArg Subtype.val
        (LB.mul_natural (p ≫ g) (p ≫ g) lam hlam (LB.inv (p ≫ g) γq) P₀)
      rw [schemeHomOverComp_coe] at this
      rw [this, TranslateCoverAux.inv_natural LB, comp_γq lam hlam lam_snd]
      have hP : schemeHomOverComp lam hlam P₀ = LB.mul (p ≫ g) γq P₀ := Subtype.ext lam_fst
      rw [hP, ← LB.mul_assoc, LB.inv_mul_cancel, LB.one_mul]
    · rw [Category.assoc, Category.id_comp]
      change lam ≫ lam' ≫ q = q
      rw [lam'_snd, lam_snd]
  have h2 : lam' ≫ lam = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      change lam' ≫ lam ≫ p = p
      rw [lam_fst]
      have := congrArg Subtype.val (LB.mul_natural (p ≫ g) (p ≫ g) lam' hlam' γq P₀)
      rw [schemeHomOverComp_coe] at this
      rw [this, comp_γq lam' hlam' lam'_snd]
      have hP : schemeHomOverComp lam' hlam' P₀ = LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀ := Subtype.ext lam'_fst
      rw [hP, ← LB.mul_assoc, LB.mul_inv_cancel, LB.one_mul]
    · rw [Category.assoc, Category.id_comp]
      change lam' ≫ lam ≫ q = q
      rw [lam_snd, lam'_snd]
  haveI : IsIso lam := ⟨⟨lam', h1, h2⟩⟩

  let W : (pullback g t₁).Opens := lam ⁻¹ᵁ (p ⁻¹ᵁ U)
  have hW : IsAffineOpen W := (hU.preimage p).preimage lam
  have hSW : ∀ b₁ : ↥(pullback g t₁), p.base b₁ ∈ S → b₁ ∈ W := by
    intro b₁ hb₁
    change p.base (lam.base b₁) ∈ U

    let β := (pullback g t₁).fromSpecResidueField b₁
    have hx : (β ≫ p) ≫ g = (β ≫ q) ≫ t₁ := by rw [Category.assoc, hpq, Category.assoc]
    have hβb : β.base (IsLocalRing.closedPoint _) = b₁ := Scheme.fromSpecResidueField_apply b₁ _
    have hxS : (β ≫ p).base (IsLocalRing.closedPoint _) ∈ S := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hβb]; exact hb₁
    have key := hS _ (β ≫ p) (β ≫ q) hx hxS

    have hβ : β ≫ (p ≫ g) = β ≫ p ≫ g := rfl
    have hnat := congrArg Subtype.val (LB.mul_natural (p ≫ g) (β ≫ p ≫ g) β hβ γq P₀)
    rw [schemeHomOverComp_coe] at hnat
    have hcongr := TranslateCoverAux.mul_coe_congr LB (show β ≫ p ≫ g = (β ≫ q) ≫ t₁ by rw [hpq, Category.assoc])
      (schemeHomOverComp β hβ γq) (schemeHomOverComp β hβ P₀)
      (schemeHomOverComp (β ≫ q) rfl γ) ⟨β ≫ p, hx⟩
      (by simp only [schemeHomOverComp_coe, γq, Category.assoc]) rfl
    have : p.base (lam.base b₁) = (β ≫ lam ≫ p).base (IsLocalRing.closedPoint _) := by
      rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp, Function.comp_apply,
        Function.comp_apply, hβb]
    rw [this, lam_fst, hnat, hcongr]
    exact key
  exact AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
    p S W hW hSW

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem (solution)
