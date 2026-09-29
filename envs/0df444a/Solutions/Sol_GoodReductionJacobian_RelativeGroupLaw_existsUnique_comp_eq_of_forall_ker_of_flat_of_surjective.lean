-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7362649b-f063-5ffe-9ce5-ced70e8607fb

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

p2m_open "CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory"
open scoped CategoryTheory.MonObj

namespace X6Aux

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}

theorem hom_one (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (φ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (⟨(L.mul t P Q).1 ≫ φ, by rw [Category.assoc, hφ]; exact (L.mul t P Q).2⟩ : SchemeHomOver t f') =
        L'.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ]; exact Q.2⟩)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (⟨(L.one t).1 ≫ φ, by rw [Category.assoc, hφ]; exact (L.one t).2⟩ : SchemeHomOver t f') = L'.one t := by
  let X : SchemeHomOver t f' := ⟨(L.one t).1 ≫ φ, by rw [Category.assoc, hφ]; exact (L.one t).2⟩
  have hXXv : (L'.mul t X X).1 = X.1 := by
    have h1 := congrArg Subtype.val (φ_hom t (L.one t) (L.one t))
    simp only at h1
    rw [L.one_mul] at h1
    exact h1.symm
  have hXX : L'.mul t X X = X := Subtype.ext hXXv
  show X = L'.one t
  calc X = L'.mul t (L'.one t) X := (L'.one_mul t X).symm
    _ = L'.mul t (L'.mul t (L'.inv t X) X) X := by rw [L'.inv_mul_cancel]
    _ = L'.mul t (L'.inv t X) (L'.mul t X X) := by rw [L'.mul_assoc]
    _ = L'.mul t (L'.inv t X) X := by rw [hXX]
    _ = L'.one t := L'.inv_mul_cancel t X

end X6Aux

theorem solution
    {R : Type u} [CommRing R] {A B C : Scheme.{u}}
    {fA : A ⟶ Spec (CommRingCat.of R)} {fB : B ⟶ Spec (CommRingCat.of R)} {fC : C ⟶ Spec (CommRingCat.of R)}
    (LA : RelativeGroupLaw R fA) (LB : RelativeGroupLaw R fB) (LC : RelativeGroupLaw R fC)
    (p : A ⟶ B) (hp : p ≫ fB = fA) [Flat p] [Surjective p] [QuasiCompact p]
    (p_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fA),
      (⟨(LA.mul t P Q).1 ≫ p, by rw [Category.assoc, hp]; exact (LA.mul t P Q).2⟩ : SchemeHomOver t fB) =
        LB.mul t ⟨P.1 ≫ p, by rw [Category.assoc, hp]; exact P.2⟩ ⟨Q.1 ≫ p, by rw [Category.assoc, hp]; exact Q.2⟩)
    (g : A ⟶ C) (hg : g ≫ fC = fA)
    (g_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fA),
      (⟨(LA.mul t P Q).1 ≫ g, by rw [Category.assoc, hg]; exact (LA.mul t P Q).2⟩ : SchemeHomOver t fC) =
        LC.mul t ⟨P.1 ≫ g, by rw [Category.assoc, hg]; exact P.2⟩ ⟨Q.1 ≫ g, by rw [Category.assoc, hg]; exact Q.2⟩)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t fA),
      (⟨P.1 ≫ p, by rw [Category.assoc, hp]; exact P.2⟩ : SchemeHomOver t fB) = LB.one t →
      (⟨P.1 ≫ g, by rw [Category.assoc, hg]; exact P.2⟩ : SchemeHomOver t fC) = LC.one t) :
    ∃ h : B ⟶ C, p ≫ h = g ∧
      (∃ hh : h ≫ fC = fB,
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fB),
          (⟨(LB.mul t P Q).1 ≫ h, by rw [Category.assoc, hh]; exact (LB.mul t P Q).2⟩ : SchemeHomOver t fC) =
            LC.mul t ⟨P.1 ≫ h, by rw [Category.assoc, hh]; exact P.2⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hh]; exact Q.2⟩) ∧
      ∀ h' : B ⟶ C, p ≫ h' = g → h' = h := by
  classical
  obtain ⟨gA, hAmul, hAone, -⟩ := LA.exists_grpObj_eq
  obtain ⟨gB, hBmul, hBone, -⟩ := LB.exists_grpObj_eq
  obtain ⟨gC, hCmul, hCone, -⟩ := LC.exists_grpObj_eq
  letI := gA; letI := gB; letI := gC
  let 𝒜 : Over (Spec (CommRingCat.of R)) := Over.mk fA
  let ℬ : Over (Spec (CommRingCat.of R)) := Over.mk fB
  let 𝒞 : Over (Spec (CommRingCat.of R)) := Over.mk fC
  let P : 𝒜 ⟶ ℬ := Over.homMk p hp
  let G : 𝒜 ⟶ 𝒞 := Over.homMk g hg
  have hPl : P.left = p := rfl
  have hGl : G.left = g := rfl
  have inj : ∀ {Y X : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} {fX : X ⟶ Spec (CommRingCat.of R)}
      (u v : Over.mk gY ⟶ Over.mk fX), overHomToSchemeHomOver u = overHomToSchemeHomOver v → u = v := by
    intro Y X gY fX u v h
    have := congrArg schemeHomOverToOverHom h
    rwa [schemeHomOverToOverHom_overHomToSchemeHomOver, schemeHomOverToOverHom_overHomToSchemeHomOver] at this

  have oneL : ∀ {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} (LX : RelativeGroupLaw R fX) [gX : GrpObj (Over.mk fX)]
      (hXone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ gX.one) = LX.one t),
      (η : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Over.mk fX).left =
        (LX.one ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom)).1 := by
    intro X fX LX gX hXone
    have := congrArg Subtype.val (hXone ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom))
    change (toUnit (𝟙_ (Over (Spec (CommRingCat.of R)))) ≫ η).left = _ at this
    rwa [toUnit_unit, Category.id_comp] at this
  let t₂ : (𝒜 ⊗ 𝒜).left ⟶ Spec (CommRingCat.of R) := (𝒜 ⊗ 𝒜).hom
  let a₁ : Over.mk t₂ ⟶ 𝒜 := fst 𝒜 𝒜
  let a₂ : Over.mk t₂ ⟶ 𝒜 := snd 𝒜 𝒜
  have mulL : (μ : 𝒜 ⊗ 𝒜 ⟶ 𝒜).left = (LA.mul t₂ (overHomToSchemeHomOver a₁) (overHomToSchemeHomOver a₂)).1 := by
    have := congrArg Subtype.val (hAmul t₂ a₁ a₂)
    change (lift (fst 𝒜 𝒜) (snd 𝒜 𝒜) ≫ μ).left = _ at this
    rwa [lift_fst_snd, Category.id_comp] at this

  have monOf : ∀ {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} (LX : RelativeGroupLaw R fX) [gX : GrpObj (Over.mk fX)]
      (hXmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk fX),
        overHomToSchemeHomOver (lift a b ≫ gX.mul) = LX.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b))
      (hXone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ gX.one) = LX.one t)
      (q : A ⟶ X) (hq : q ≫ fX = fA)
      (q_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t fA),
        (⟨(LA.mul t P Q).1 ≫ q, by rw [Category.assoc, hq]; exact (LA.mul t P Q).2⟩ : SchemeHomOver t fX) =
          LX.mul t ⟨P.1 ≫ q, by rw [Category.assoc, hq]; exact P.2⟩ ⟨Q.1 ≫ q, by rw [Category.assoc, hq]; exact Q.2⟩),
      IsMonHom (Over.homMk q hq : 𝒜 ⟶ Over.mk fX) := by
    intro X fX LX gX hXmul hXone q hq q_hom
    let qq : 𝒜 ⟶ Over.mk fX := Over.homMk q hq
    show IsMonHom qq
    refine ⟨?_, ?_⟩
    · apply Over.OverMorphism.ext
      rw [Over.comp_left, oneL LA hAone, oneL LX hXone]
      exact congrArg Subtype.val (X6Aux.hom_one LA LX q hq q_hom _)
    · apply Over.OverMorphism.ext
      have eR : (qq ⊗ₘ qq) ≫ (μ : Over.mk fX ⊗ Over.mk fX ⟶ Over.mk fX) = lift (fst 𝒜 𝒜 ≫ qq) (snd 𝒜 𝒜 ≫ qq) ≫ μ := by
        rw [← lift_map, lift_fst_snd, Category.id_comp]
      rw [eR, Over.comp_left, mulL]
      change (LA.mul t₂ (overHomToSchemeHomOver a₁) (overHomToSchemeHomOver a₂)).1 ≫ q =
        (lift (a₁ ≫ qq) (a₂ ≫ qq) ≫ (μ : Over.mk fX ⊗ Over.mk fX ⟶ Over.mk fX)).left
      have hq1 := congrArg Subtype.val (q_hom t₂ (overHomToSchemeHomOver a₁) (overHomToSchemeHomOver a₂))
      simp only at hq1
      rw [hq1]
      have := congrArg Subtype.val (hXmul t₂ (a₁ ≫ qq) (a₂ ≫ qq))
      rw [overHomToSchemeHomOver_coe] at this
      rw [this]
      exact congrArg Subtype.val (congrArg₂ (LX.mul t₂) (Subtype.ext rfl) (Subtype.ext rfl))
  haveI : IsMonHom P := monOf LB hBmul hBone p hp p_hom
  haveI : IsMonHom G := monOf LC hCmul hCone g hg g_hom
  haveI : Flat P.left := ‹Flat p›
  haveI : Surjective P.left := ‹Surjective p›
  haveI : QuasiCompact P.left := ‹QuasiCompact p›

  have hker' : ∀ (T : Over (Spec (CommRingCat.of R))) (a : T ⟶ 𝒜), a ≫ P = 1 → a ≫ G = 1 := by
    intro T a ha
    let a' : Over.mk T.hom ⟶ 𝒜 := a
    have h1 : (⟨(overHomToSchemeHomOver a').1 ≫ p, by
          rw [Category.assoc, hp]; exact (overHomToSchemeHomOver a').2⟩ : SchemeHomOver T.hom fB) = LB.one T.hom := by
      apply Subtype.ext
      have := congrArg (fun k => Over.Hom.left k) ha
      simp only [Over.comp_left] at this
      change a.left ≫ p = (toUnit (Over.mk T.hom) ≫ (η : _ ⟶ ℬ)).left at this
      show a.left ≫ p = (LB.one T.hom).1
      rw [this]
      exact congrArg Subtype.val (hBone T.hom)
    have h2 := congrArg Subtype.val (hker T.hom (overHomToSchemeHomOver a') h1)
    apply Over.OverMorphism.ext
    change a.left ≫ g = (toUnit (Over.mk T.hom) ≫ (η : _ ⟶ 𝒞)).left
    rw [show a.left ≫ g = (LC.one T.hom).1 from h2]
    exact (congrArg Subtype.val (hCone T.hom)).symm
  obtain ⟨h, hmon, hPh, huniq⟩ :=
    AlgebraicGeometry.exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective P G hker'
  have hhl : (h.left : B ⟶ C) ≫ fC = fB := Over.w h
  refine ⟨h.left, ?_, ⟨hhl, ?_⟩, ?_⟩
  · have := congrArg (fun k => k.left) hPh
    simp [Over.comp_left] at this
    exact this
  · intro T t Pt Qt
    let a : Over.mk t ⟶ ℬ := schemeHomOverToOverHom Pt
    let b : Over.mk t ⟶ ℬ := schemeHomOverToOverHom Qt
    have key := congrArg (overHomToSchemeHomOver (Y := T) (g := t)) (show lift a b ≫ μ ≫ h = lift (a ≫ h) (b ≫ h) ≫ μ by
      rw [hmon.mul_hom, ← Category.assoc, lift_map])
    rw [hCmul] at key
    have e1 : overHomToSchemeHomOver (Y := T) (g := t) (lift a b ≫ μ ≫ h) =
        ⟨(LB.mul t Pt Qt).1 ≫ (h.left : B ⟶ C), by
          rw [Category.assoc]; exact (congrArg ((LB.mul t Pt Qt).1 ≫ ·) hhl).trans (LB.mul t Pt Qt).2⟩ := by
      apply Subtype.ext
      show (lift a b ≫ μ ≫ h).left = (LB.mul t Pt Qt).1 ≫ h.left
      rw [← Category.assoc, Over.comp_left, ← overHomToSchemeHomOver_coe (lift a b ≫ μ), hBmul]
      simp [a, b, overHomToSchemeHomOver_schemeHomOverToOverHom]
      try rfl
    rw [e1] at key
    rw [key]
    congr 1 <;> apply Subtype.ext <;> simp [a, b, Over.comp_left]
  · intro h' hh'
    haveI : Epi p := AlgebraicGeometry.Flat.epi_of_flat_of_surjective p
    have hh'C : h' ≫ fC = fB := by
      rw [← cancel_epi p, ← Category.assoc, hh', hg, hp]
    let H' : ℬ ⟶ 𝒞 := Over.homMk h' hh'C
    have : H' = h := huniq H' (Over.OverMorphism.ext (by simp [Over.comp_left] at hh' ⊢; exact hh'))
    exact (congrArg (fun k => k.left) this : H'.left = h.left)

end S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_ker_of_flat_of_surjective (solution)
