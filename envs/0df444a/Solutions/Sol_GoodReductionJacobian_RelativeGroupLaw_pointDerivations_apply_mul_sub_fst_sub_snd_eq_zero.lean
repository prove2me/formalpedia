-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4b2cd1da-3278-5ce2-89f5-357a4751ed84

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Theorems.Thm_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (Ue : A.Opens)
    (U' : (pullback f f).Opens) (hU' : IsAffineOpen U')
    (hU₁ : U' ≤ pullback.fst f f ⁻¹ᵁ Ue) (hU₂ : U' ≤ pullback.snd f f ⁻¹ᵁ Ue)
    (hUμ : U' ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ Ue)
    (eP : Spec (CommRingCat.of k) ⟶ (U' : Scheme.{u}))
    (heP₁ : eP ≫ U'.ι ≫ pullback.fst f f = (L.one (𝟙 _)).1) (heP₂ : eP ≫ U'.ι ≫ pullback.snd f f = (L.one (𝟙 _)).1)
    (M : Type u) [AddCommGroup M] [Module k M]
    (D : letI := algebraOfHom (pullback.fst f f ≫ f) U'
      ↥(Algebra.PointDerivations k Γ(pullback f f, U')
          ((U'.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) M))
    (a : Γ(A, Ue)) :
    D.1 (((pullback f f).presheaf.map (homOfLE hUμ).op).hom
            (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₁).op).hom (((pullback.fst f f).app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₂).op).hom (((pullback.snd f f).app Ue).hom a)) = 0 := by
  classical

  letI : Module kᵐᵒᵖ M := Module.compHom M ((RingHom.id k).fromOpposite fun a b => mul_comm a b)
  haveI : IsCentralScalar k M := ⟨fun _ _ => rfl⟩

  set μP := L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩ with hμP
  have he : (L.one (𝟙 _)).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  have heP : eP ≫ U'.ι ≫ (pullback.fst f f ≫ f) = 𝟙 _ := by
    have : (eP ≫ U'.ι ≫ pullback.fst f f) ≫ f = 𝟙 _ := by rw [heP₁, he]
    simpa only [Category.assoc] using this

  obtain ⟨v, hv, hvr⟩ := AlgebraicGeometry.exists_tangentPoints_appLE_eq_of_pointDerivations (pullback.fst f f ≫ f) U' hU' eP heP M D

  let v₁ : TangentPoints f (L.one (𝟙 _)).1 M :=
    ⟨v.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact v.2.1, by rw [← Category.assoc, v.2.2, Category.assoc, heP₁]⟩
  let v₂ : TangentPoints f (L.one (𝟙 _)).1 M :=
    ⟨v.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact v.2.1,
      by rw [← Category.assoc, v.2.2, Category.assoc, heP₂]⟩
  have hmul : v.1 ≫ μP.1 = (L.mul (SquareZero.toBase k M) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1 := by
    have := L.mul_natural (pullback.fst f f ≫ f) (SquareZero.toBase k M) v.1 v.2.1
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
    have h' := congrArg Subtype.val this
    simp only [schemeHomOverComp_coe] at h'
    rw [hμP]
    exact h'

  have hpre : ∀ (g : pullback f f ⟶ A) (hg : U' ≤ g ⁻¹ᵁ Ue), ⊤ ≤ (v.1 ≫ g) ⁻¹ᵁ Ue := by
    intro g hg p _
    have hp : p ∈ v.1 ⁻¹ᵁ U' := hv (Set.mem_univ p)
    exact hg hp
  have h₁ : ⊤ ≤ v₁.1 ⁻¹ᵁ Ue := hpre _ hU₁
  have h₂ : ⊤ ≤ v₂.1 ⁻¹ᵁ Ue := hpre _ hU₂
  have hμ' : ⊤ ≤ (v.1 ≫ μP.1) ⁻¹ᵁ Ue := hpre _ hUμ
  have hμ : ⊤ ≤ (L.mul (SquareZero.toBase k M) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1 ⁻¹ᵁ Ue := by rw [← hmul]; exact hμ'

  have hadd := GoodReductionJacobian.RelativeGroupLaw.snd_appLE_mul_tangentPoints_eq_add f L M v₁ v₂ Ue a h₁ h₂ hμ

  have hread : ∀ (g : pullback f f ⟶ A) (hg : U' ≤ g ⁻¹ᵁ Ue) (h : ⊤ ≤ (v.1 ≫ g) ⁻¹ᵁ Ue),
      (((v.1 ≫ g).appLE Ue ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt k M))).hom).hom a).snd =
        D.1 (((pullback f f).presheaf.map (homOfLE hg).op).hom ((g.app Ue).hom a)) := by
    intro g hg h
    have e1 : (v.1 ≫ g).appLE Ue ⊤ h = g.appLE Ue U' hg ≫ v.1.appLE U' ⊤ hv := by
      rw [Scheme.Hom.appLE_comp_appLE]
    rw [e1, Category.assoc, CommRingCat.comp_apply]
    erw [hvr]
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl
  have rμ := hread μP.1 hUμ hμ'
  have r₁ := hread (pullback.fst f f) hU₁ h₁
  have r₂ := hread (pullback.snd f f) hU₂ h₂

  have hcongr : ∀ {g₁ g₂ : SquareZero.spec k M ⟶ A} (e : g₁ = g₂) (hh₁ : ⊤ ≤ g₁ ⁻¹ᵁ Ue) (hh₂ : ⊤ ≤ g₂ ⁻¹ᵁ Ue),
      g₁.appLE Ue ⊤ hh₁ = g₂.appLE Ue ⊤ hh₂ := by
    intro g₁ g₂ e hh₁ hh₂; subst e; rfl
  rw [hcongr hmul hμ' hμ] at rμ
  have r₁' : (((v₁.1).appLE Ue ⊤ h₁ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt k M))).hom).hom a).snd =
      D.1 (((pullback f f).presheaf.map (homOfLE hU₁).op).hom (((pullback.fst f f).app Ue).hom a)) := r₁
  have r₂' : (((v₂.1).appLE Ue ⊤ h₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt k M))).hom).hom a).snd =
      D.1 (((pullback f f).presheaf.map (homOfLE hU₂).op).hom (((pullback.snd f f).app Ue).hom a)) := r₂
  have key : D.1 (((pullback f f).presheaf.map (homOfLE hUμ).op).hom ((μP.1.app Ue).hom a)) =
      D.1 (((pullback f f).presheaf.map (homOfLE hU₁).op).hom (((pullback.fst f f).app Ue).hom a)) +
      D.1 (((pullback f f).presheaf.map (homOfLE hU₂).op).hom (((pullback.snd f f).app Ue).hom a)) := by
    rw [← rμ, ← r₁', ← r₂']
    exact hadd
  rw [map_sub, map_sub, key]
  abel

end S_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero (solution)
