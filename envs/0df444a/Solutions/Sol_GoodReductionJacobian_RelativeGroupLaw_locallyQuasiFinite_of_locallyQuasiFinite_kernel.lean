-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_of_locallyQuasiFinite_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/48380c6a-d6cd-50e5-8e6f-1495ad2fde0d

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 800000

theorem solution
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (LB : RelativeGroupLaw R g) (L : RelativeGroupLaw R f) (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    [LocallyOfFiniteType g]
    [LocallyQuasiFinite (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)]
    [QuasiCompact (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)] :
    LocallyQuasiFinite u.1 := by

  have he : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

  have hfin : ∀ b : B, ((pullback.fst g (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)) ⁻¹'
      {b}).Finite := fun b => Scheme.Hom.finite_preimage_singleton _ b

  have hcondP := pullback.condition (f := g) (g := pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
  have hcondK := pullback.condition (f := u.1) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
  let tP := pullback.fst g (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ g
  let x₁ : SchemeHomOver tP g := ⟨pullback.fst _ _, rfl⟩
  have hx₂ : (pullback.snd g (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
      pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ g = tP := by
    calc _ = pullback.snd g (pullback.snd u.1 (L.one (𝟙 _)).1) ≫
          (pullback.fst u.1 (L.one (𝟙 _)).1 ≫ u.1) ≫ f := by simp only [Category.assoc, u.2]
      _ = pullback.snd g (pullback.snd u.1 (L.one (𝟙 _)).1) ≫ pullback.snd u.1 (L.one (𝟙 _)).1 := by
          rw [hcondK, Category.assoc, he, Category.comp_id]
      _ = tP := hcondP.symm
  let x₂ : SchemeHomOver tP g := ⟨_, hx₂⟩
  have hx₂u : NeronModelInfra.schemeHomOverComp x₂ u = L.one tP := by
    rw [← L.one_natural (𝟙 _) tP (pullback.snd g (pullback.snd u.1 (L.one (𝟙 _)).1) ≫
      pullback.snd u.1 (L.one (𝟙 _)).1) (by rw [Category.comp_id]; exact hcondP.symm)]
    apply Subtype.ext
    show (pullback.snd g _ ≫ pullback.fst u.1 _) ≫ u.1 = (pullback.snd g _ ≫ pullback.snd u.1 _) ≫ _
    rw [Category.assoc, hcondK, Category.assoc]
  have hm : (LB.mul tP x₁ x₂).1 ≫ u.1 = pullback.fst g _ ≫ u.1 := by
    have := hu tP x₁ x₂
    rw [hx₂u, L.mul_one] at this
    exact congrArg Subtype.val this
  let σ : pullback g (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ⟶ pullback u.1 u.1 :=
    pullback.lift (pullback.fst _ _) (LB.mul tP x₁ x₂).1 hm.symm
  have hσ₁ : σ ≫ pullback.fst u.1 u.1 = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pullback.snd u.1 u.1 = (LB.mul tP x₁ x₂).1 := pullback.lift_snd _ _ _

  have hcondQ := pullback.condition (f := u.1) (g := u.1)
  let tQ := pullback.fst u.1 u.1 ≫ g
  let y₁ : SchemeHomOver tQ g := ⟨pullback.fst u.1 u.1, rfl⟩
  have hy₂ : pullback.snd u.1 u.1 ≫ g = tQ := by
    show _ ≫ g = pullback.fst u.1 u.1 ≫ g
    calc pullback.snd u.1 u.1 ≫ g = pullback.snd u.1 u.1 ≫ u.1 ≫ f := by rw [u.2]
      _ = pullback.fst u.1 u.1 ≫ u.1 ≫ f := by rw [← Category.assoc, ← hcondQ, Category.assoc]
      _ = _ := by rw [u.2]
  let y₂ : SchemeHomOver tQ g := ⟨pullback.snd u.1 u.1, hy₂⟩
  let d : SchemeHomOver tQ g := LB.mul tQ (LB.inv tQ y₁) y₂
  have hd : NeronModelInfra.schemeHomOverComp d u = L.one tQ := by
    letI := LB.pointGroup tQ
    letI := L.pointGroup tQ
    let φ : SchemeHomOver tQ g →* SchemeHomOver tQ f :=
      MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x u) (hu tQ)
    have hy : φ y₂ = φ y₁ := by
      apply Subtype.ext
      show pullback.snd u.1 u.1 ≫ u.1 = pullback.fst u.1 u.1 ≫ u.1
      exact hcondQ.symm
    show φ (y₁⁻¹ * y₂) = 1
    rw [map_mul, map_inv, hy, _root_.inv_mul_cancel]
  have hone : (L.one tQ).1 = tQ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    rw [← L.one_natural (𝟙 _) tQ tQ (Category.comp_id _)]
    rfl
  let k : pullback u.1 u.1 ⟶ pullback u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    pullback.lift d.1 tQ (by rw [← hone, ← hd]; rfl)
  have hk₁ : k ≫ pullback.fst _ _ = d.1 := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd _ _ = tQ := pullback.lift_snd _ _ _
  let τ : pullback u.1 u.1 ⟶ pullback g (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) :=
    pullback.lift (pullback.fst u.1 u.1) k (by rw [hk₂])
  have hτ₁ : τ ≫ pullback.fst _ _ = pullback.fst u.1 u.1 := pullback.lift_fst _ _ _
  have hτ₂ : τ ≫ pullback.snd _ _ = k := pullback.lift_snd _ _ _
  have hτt : τ ≫ tP = tQ := by
    show τ ≫ pullback.fst _ _ ≫ g = pullback.fst u.1 u.1 ≫ g
    rw [← Category.assoc, hτ₁]
  have hτσ : τ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσ₁, hτ₁, Category.id_comp]
    · rw [Category.assoc, hσ₂, Category.id_comp]
      have hnat := LB.mul_natural tP tQ τ hτt x₁ x₂
      have e₁ : GoodReductionJacobian.schemeHomOverComp τ hτt x₁ = y₁ := Subtype.ext hτ₁
      have e₂ : GoodReductionJacobian.schemeHomOverComp τ hτt x₂ = d := by
        apply Subtype.ext
        show τ ≫ pullback.snd g _ ≫ pullback.fst u.1 _ = d.1
        rw [← Category.assoc, hτ₂, hk₁]
      rw [e₁, e₂] at hnat
      have hgrp : LB.mul tQ y₁ d = y₂ := by
        letI := LB.pointGroup tQ
        show y₁ * (y₁⁻¹ * y₂) = y₂
        exact mul_inv_cancel_left y₁ y₂
      rw [hgrp] at hnat
      exact congrArg Subtype.val hnat
  have hσsurj : Function.Surjective σ := fun z =>
    ⟨τ z, by rw [← Scheme.Hom.comp_apply, hτσ]; rfl⟩

  haveI : LocallyOfFiniteType u.1 := by
    have : LocallyOfFiniteType (u.1 ≫ f) := by rw [u.2]; infer_instance
    exact locallyOfFiniteType_of_comp u.1 f
  refine LocallyQuasiFinite.of_finite_preimage_singleton u.1 fun y => ?_
  by_cases hy : (u.1 ⁻¹' {y} : Set B).Nonempty
  · obtain ⟨b₀, hb₀ : u.1 b₀ = y⟩ := hy
    refine (((hfin b₀).image σ).image (pullback.snd u.1 u.1)).subset fun b (hb : u.1 b = y) => ?_
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback b₀ b (hb₀.trans hb.symm)
    refine ⟨z, ⟨τ z, ?_, ?_⟩, hz₂⟩
    · show (pullback.fst g (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)) (τ z) = b₀
      rw [← Scheme.Hom.comp_apply, hτ₁, hz₁]
    · rw [← Scheme.Hom.comp_apply, hτσ]; rfl
  · rw [Set.not_nonempty_iff_eq_empty.mp hy]
    exact Set.finite_empty

end S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel (solution)
