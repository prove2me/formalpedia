-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6abe9e72-f052-5699-8ed2-64a188520f98

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKernelQuasiFinite

section Hom

variable {R : Type u} [CommRing R] {G H : Scheme.{u}}
  {gG : G ⟶ Spec (CommRingCat.of R)} {gH : H ⟶ Spec (CommRingCat.of R)}

noncomputable def pointHom (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := LG.pointGroup t
    letI := LH.pointGroup t
    SchemeHomOver t gG →* SchemeHomOver t gH :=
  letI := LG.pointGroup t
  letI := LH.pointGroup t
  MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x u) (fun x y => hu t x y)

theorem hom_one (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LG.one t) u = LH.one t := by
  letI := LG.pointGroup t
  letI := LH.pointGroup t
  exact (pointHom LG LH u hu t).map_one

theorem hom_inv (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t gG) :
    NeronModelInfra.schemeHomOverComp (LG.inv t x) u =
      LH.inv t (NeronModelInfra.schemeHomOverComp x u) := by
  letI := LG.pointGroup t
  letI := LH.pointGroup t
  exact (pointHom LG LH u hu t).map_inv x

theorem finite_setOf_schemeHomOverComp_eq (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hfin : {x : SchemeHomOver t gG | NeronModelInfra.schemeHomOverComp x u = LH.one t}.Finite)
    (c : SchemeHomOver t gH) :
    {x : SchemeHomOver t gG | NeronModelInfra.schemeHomOverComp x u = c}.Finite := by
  letI := LG.pointGroup t
  letI := LH.pointGroup t
  by_cases hne : {x : SchemeHomOver t gG | NeronModelInfra.schemeHomOverComp x u = c}.Nonempty
  · obtain ⟨b₀, hb₀⟩ := hne
    let φ := pointHom LG LH u hu t
    have hφ : ∀ x, φ x = NeronModelInfra.schemeHomOverComp x u := fun _ => rfl

    refine Set.Finite.of_finite_image (f := fun x => x * b₀⁻¹) (hfin.subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_setOf_eq] at hx hb₀ ⊢
      rw [← hφ] at hx hb₀ ⊢
      rw [map_mul, map_inv, hx, hb₀, mul_inv_cancel]
      rfl
    · intro x _ y _ hxy
      exact mul_right_cancel hxy
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

end Hom

theorem finite_of_finite_closedPoints {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    (h : (closedPoints X).Finite) : Finite X := by
  have hcl : IsClosed (closedPoints X) := by
    have : closedPoints X = ⋃ x ∈ closedPoints X, {x} := by
      ext x; simp
    rw [this]
    exact h.isClosed_biUnion fun x hx => hx
  have huniv : closedPoints X = Set.univ := by
    rw [← hcl.closure_eq]
    exact closure_closedPoints
  rw [huniv] at h
  exact Set.finite_univ_iff.mp h

section Fibre

variable {R : Type u} [CommRing R] {G H : Scheme.{u}}
  {gG : G ⟶ Spec (CommRingCat.of R)} {gH : H ⟶ Spec (CommRingCat.of R)}

theorem preimage_singleton_subset_range_fst (u : G ⟶ H) {Ω : Type u} [Field Ω]
    (ybar : Spec (CommRingCat.of Ω) ⟶ H) (y : H) (hybar : ∀ s, ybar s = y) :
    u ⁻¹' {y} ⊆ Set.range (pullback.fst u ybar) := by
  intro x hx
  have hx' : u x = ybar (IsLocalRing.closedPoint Ω) := by
    rw [hybar]; exact hx
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := ybar) x _ hx'
  exact ⟨z, hz⟩

theorem finite_sections_pullback (u : SchemeHomOver gG gH)
    {Ω : Type u} [Field Ω] (ybar : Spec (CommRingCat.of Ω) ⟶ H)
    (hfin : {x : SchemeHomOver (ybar ≫ gH) gG |
      NeronModelInfra.schemeHomOverComp x u = ⟨ybar, rfl⟩}.Finite) :
    Finite {p : Spec (CommRingCat.of Ω) ⟶ pullback u.1 ybar // p ≫ pullback.snd u.1 ybar = 𝟙 _} := by
  classical

  let σ : {p : Spec (CommRingCat.of Ω) ⟶ pullback u.1 ybar // p ≫ pullback.snd u.1 ybar = 𝟙 _} →
      SchemeHomOver (ybar ≫ gH) gG := fun p =>
    ⟨p.1 ≫ pullback.fst u.1 ybar, by
      calc (p.1 ≫ pullback.fst u.1 ybar) ≫ gG
          = p.1 ≫ (pullback.fst u.1 ybar ≫ u.1) ≫ gH := by
            simp only [Category.assoc]; rw [u.2]
        _ = p.1 ≫ (pullback.snd u.1 ybar ≫ ybar) ≫ gH := by rw [pullback.condition]
        _ = (p.1 ≫ pullback.snd u.1 ybar) ≫ ybar ≫ gH := by simp only [Category.assoc]
        _ = ybar ≫ gH := by rw [p.2, Category.id_comp]⟩
  have hσ_inj : Function.Injective σ := by
    intro p q hpq
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hpq
    · rw [p.2, q.2]
  have hσ_mem : ∀ p, σ p ∈ {x : SchemeHomOver (ybar ≫ gH) gG |
      NeronModelInfra.schemeHomOverComp x u = ⟨ybar, rfl⟩} := by
    intro p
    simp only [Set.mem_setOf_eq]
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, σ, Category.assoc]
    rw [pullback.condition, ← Category.assoc, p.2, Category.id_comp]
  have : Finite {x : SchemeHomOver (ybar ≫ gH) gG |
      NeronModelInfra.schemeHomOverComp x u = ⟨ybar, rfl⟩} := hfin
  exact Finite.of_injective (fun p => (⟨σ p, hσ_mem p⟩ : {x : SchemeHomOver (ybar ≫ gH) gG |
      NeronModelInfra.schemeHomOverComp x u = ⟨ybar, rfl⟩}))
      (fun p q hpq => hσ_inj (congrArg Subtype.val hpq))

theorem finite_pullback [LocallyOfFiniteType gG] (u : SchemeHomOver gG gH)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ybar : Spec (CommRingCat.of Ω) ⟶ H)
    (hfin : {x : SchemeHomOver (ybar ≫ gH) gG |
      NeronModelInfra.schemeHomOverComp x u = ⟨ybar, rfl⟩}.Finite) :
    Finite ↥(pullback u.1 ybar) := by
  have hlft : LocallyOfFiniteType u.1 := by
    have : LocallyOfFiniteType (u.1 ≫ gH) := by rw [u.2]; infer_instance
    exact locallyOfFiniteType_of_comp u.1 gH
  have : JacobsonSpace ↥(pullback u.1 ybar) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd u.1 ybar)
  apply finite_of_finite_closedPoints
  have hsec := finite_sections_pullback u ybar hfin
  have : Finite (closedPoints ↥(pullback u.1 ybar)) :=
    Finite.of_equiv _ (pointEquivClosedPoint (pullback.snd u.1 ybar))
  exact Set.toFinite _

end Fibre

end P2mKernelQuasiFinite

open P2mKernelQuasiFinite in
theorem solution
    {R : Type u} [CommRing R] {G H : Scheme.{u}}
    {gG : G ⟶ Spec (CommRingCat.of R)} {gH : H ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType gG]
    (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
      {x : SchemeHomOver t gG | NeronModelInfra.schemeHomOverComp x u = LH.one t}.Finite) :
    LocallyQuasiFinite u.1 := by
  have hlft : LocallyOfFiniteType u.1 := by
    have : LocallyOfFiniteType (u.1 ≫ gH) := by rw [u.2]; infer_instance
    exact locallyOfFiniteType_of_comp u.1 gH
  refine LocallyQuasiFinite.of_finite_preimage_singleton u.1 fun y => ?_

  let Ω : Type u := AlgebraicClosure (H.residueField y)
  let ybar : Spec (CommRingCat.of Ω) ⟶ H :=
    Spec.map (CommRingCat.ofHom (algebraMap (H.residueField y) Ω)) ≫ H.fromSpecResidueField y
  have hybar : ∀ s, ybar s = y := fun s => by
    simp only [ybar, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    exact H.fromSpecResidueField_apply y _
  have hF : Finite ↥(pullback u.1 ybar) :=
    finite_pullback u ybar
      (finite_setOf_schemeHomOverComp_eq LG LH u hu (ybar ≫ gH) (hfin Ω (ybar ≫ gH)) ⟨ybar, rfl⟩)
  exact (Set.finite_range (pullback.fst u.1 ybar)).subset
    (preimage_singleton_subset_range_fst u.1 ybar y hybar)

end S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one (solution)
