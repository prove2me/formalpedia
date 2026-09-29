-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8df6d34f-f9e1-5029-b4be-e0c1715fe1a5

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace R4InfNil

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

theorem isInfinitesimal_iff_val (L : RelativeGroupLaw B f) {R : Type} [CommRing R] [Algebra B R]
    (J : Ideal R) (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) R) f) :
    L.IsInfinitesimal J Q ↔
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom) ≫ Q.1 =
        (L.one (Scheme.specOver (𝒪 := B) (R ⧸ J))).1 := by
  unfold RelativeGroupLaw.IsInfinitesimal
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem specMap_comp_one_val (L : RelativeGroupLaw B f) {R : Type} [CommRing R] [Algebra B R]
    {R' : Type} [CommRing R'] [Algebra B R'] (g : R →ₐ[B] R') :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (L.one (Scheme.specOver (𝒪 := B) R)).1 =
      (L.one (Scheme.specOver (𝒪 := B) R')).1 := by
  have h := L.one_natural (Scheme.specOver (𝒪 := B) R) (Scheme.specOver (𝒪 := B) R')
    (Spec.map (CommRingCat.ofHom g.toRingHom)) (Scheme.specMap_algHom_comp_specOver g)
  exact congrArg Subtype.val h

theorem forall_field_of_isInfinitesimal (L : RelativeGroupLaw B f) {R : Type} [CommRing R] [Algebra B R]
    (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) R) f)
    (h : L.IsInfinitesimal (nilradical R) Q)
    (κ : Type) [Field κ] [Algebra B κ] (φ : R →ₐ[B] κ) :
    schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (Scheme.specMap_algHom_comp_specOver φ) Q = L.one (Scheme.specOver (𝒪 := B) κ) := by
  apply Subtype.ext
  rw [schemeHomOverComp_coe]

  have hker : ∀ a ∈ nilradical R, φ a = 0 := by
    intro a ha
    exact ((mem_nilradical.mp ha).map φ).eq_zero
  let φbar : (R ⧸ nilradical R) →ₐ[B] κ := Ideal.Quotient.liftₐ (nilradical R) φ hker
  have hring : CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (Ideal.Quotient.mkₐ B (nilradical R)).toRingHom ≫ CommRingCat.ofHom φbar.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  rw [hring, Spec.map_comp, Category.assoc, (isInfinitesimal_iff_val L (nilradical R) Q).mp h]
  exact specMap_comp_one_val L φbar

theorem isInfinitesimal_of_forall_field (L : RelativeGroupLaw B f) [IsSeparated f]
    {R : Type} [CommRing R] [Algebra B R]
    (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) R) f)
    (hall : ∀ (κ : Type) [Field κ] [Algebra B κ] (φ : R →ₐ[B] κ),
      schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (Scheme.specMap_algHom_comp_specOver φ) Q = L.one (Scheme.specOver (𝒪 := B) κ)) :
    L.IsInfinitesimal (nilradical R) Q := by
  rw [isInfinitesimal_iff_val]

  haveI hred : _root_.IsReduced (R ⧸ nilradical R) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical (⊥ : Ideal R))
  haveI : IsReduced (Spec (CommRingCat.of (R ⧸ nilradical R))) := inferInstance
  refine ext_of_fromSpecResidueField_eq _ _ f Set.univ dense_univ ?_ ?_
  · intro x _
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((Spec (CommRingCat.of (R ⧸ nilradical R))).fromSpecResidueField x)
    rw [← hψ]

    let κ : Type := (Spec (CommRingCat.of (R ⧸ nilradical R))).residueField x
    let φ' : R →+* κ := ψ.hom.comp (Ideal.Quotient.mk (nilradical R))
    letI : Algebra B κ := (φ'.comp (algebraMap B R)).toAlgebra
    let φ : R →ₐ[B] κ :=
      { φ' with
        commutes' := fun b => rfl }
    have key := congrArg Subtype.val (hall κ φ)
    rw [schemeHomOverComp_coe] at key
    have hring : CommRingCat.ofHom φ.toRingHom =
        CommRingCat.ofHom (Ideal.Quotient.mkₐ B (nilradical R)).toRingHom ≫ ψ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      rfl
    rw [hring, Spec.map_comp, Category.assoc] at key
    rw [key]

    have hover : Spec.map ψ ≫ Scheme.specOver (𝒪 := B) (R ⧸ nilradical R) = Scheme.specOver (𝒪 := B) κ := by
      change Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap B (R ⧸ nilradical R))) =
        Spec.map (CommRingCat.ofHom (algebraMap B κ))
      rw [← Spec.map_comp]
      rfl
    have hone := L.one_natural (Scheme.specOver (𝒪 := B) (R ⧸ nilradical R)) (Scheme.specOver (𝒪 := B) κ)
      (Spec.map ψ) hover
    exact (congrArg Subtype.val hone).symm
  · rw [Category.assoc, Q.2, (L.one (Scheme.specOver (𝒪 := B) (R ⧸ nilradical R))).2]
    exact Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B (nilradical R))

end R4InfNil

open R4InfNil in
theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) [IsSeparated f]
    (R : Type) [CommRing R] [Algebra B R] (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) R) f) :
    L.IsInfinitesimal (nilradical R) Q ↔
      ∀ (κ : Type) [Field κ] [Algebra B κ] (φ : R →ₐ[B] κ),
        schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
          (Scheme.specMap_algHom_comp_specOver φ) Q = L.one (Scheme.specOver (𝒪 := B) κ) :=
  ⟨fun h κ _ _ φ => forall_field_of_isInfinitesimal L Q h κ φ,
    fun h => isInfinitesimal_of_forall_field L Q h⟩

end S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one (solution)
