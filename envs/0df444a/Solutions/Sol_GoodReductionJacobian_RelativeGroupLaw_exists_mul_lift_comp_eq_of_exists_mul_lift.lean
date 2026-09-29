-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_comp_eq_of_exists_mul_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1df6b24b-f2b2-5c3c-abe3-528dc46f19b1

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_comp_eq_of_exists_mul_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem solution
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)
    (m' : pullback f f ⟶ A) (hm'f : m' ≫ f = pullback.fst f f ≫ f)
    (hm'μ : pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ m' =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g) :
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      pullback.lift e.1 e.1 rfl ≫ m = e.1 ∧
      pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ m =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by
  haveI := hs
  haveI : LocallyOfFinitePresentation f := inferInstance
  haveI : Flat f := inferInstance
  have hef : e.1 ≫ f = 𝟙 _ := e.2
  have he₀f : (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ f₀ = 𝟙 _ := (L₀.one (𝟙 (Spec (CommRingCat.of T)))).2
  have hlift : 𝟙 A ≫ f = (f ≫ e.1) ≫ f := by
    rw [Category.id_comp, Category.assoc, hef, Category.comp_id]
  have hlift₀ : 𝟙 A₀ ≫ f₀ = (f₀ ≫ (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1) ≫ f₀ := by
    rw [Category.id_comp, Category.assoc, he₀f, Category.comp_id]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : A ⟶ A, ρ = pullback.lift (𝟙 A) (f ≫ e.1) hlift ≫ m' := ⟨_, rfl⟩
  have hρf : ρ ≫ f = f := by
    rw [hρ, Category.assoc, hm'f, ← Category.assoc, pullback.lift_fst, Category.id_comp]

  obtain ⟨s, hsdef⟩ : ∃ s : A₀ ⟶ pullback f₀ f₀,
      s = pullback.lift (𝟙 A₀) (f₀ ≫ (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1) hlift₀ := ⟨_, rfl⟩
  have hs₁ : s ≫ pullback.fst f₀ f₀ = 𝟙 A₀ := by rw [hsdef, pullback.lift_fst]
  have hs₂ : s ≫ pullback.snd f₀ f₀ = f₀ ≫ (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 := by
    rw [hsdef, pullback.lift_snd]
  have hsG : s ≫ pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])
      = g ≫ pullback.lift (𝟙 A) (f ≫ e.1) hlift := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hs₁, Category.id_comp,
        Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hs₂, Category.assoc, ← he,
        Category.assoc, pullback.lift_snd, ← Category.assoc, ← hg.w, Category.assoc]
  have hst : s ≫ (pullback.fst f₀ f₀ ≫ f₀) = f₀ := by rw [← Category.assoc, hs₁, Category.id_comp]
  have hsμ : s ≫ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩
      ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 = 𝟙 A₀ := by
    have hnat := L₀.mul_natural (pullback.fst f₀ f₀ ≫ f₀) f₀ s hst ⟨pullback.fst f₀ f₀, rfl⟩
      ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩
    have h1 : schemeHomOverComp s hst ⟨pullback.fst f₀ f₀, rfl⟩ = (⟨𝟙 A₀, Category.id_comp f₀⟩ : SchemeHomOver f₀ f₀) := by
      apply Subtype.ext; rw [schemeHomOverComp_coe]; exact hs₁
    have h2 : schemeHomOverComp s hst ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩ = L₀.one f₀ := by
      rw [← L₀.one_natural (𝟙 _) f₀ f₀ (Category.comp_id _)]
      apply Subtype.ext; rw [schemeHomOverComp_coe, schemeHomOverComp_coe]; exact hs₂
    have h3 := congrArg Subtype.val hnat
    rw [schemeHomOverComp_coe, h1, h2, L₀.mul_one] at h3
    exact h3
  have hgρ : g ≫ ρ = g := by
    rw [hρ, ← Category.assoc, ← hsG, Category.assoc, hm'μ, ← Category.assoc, hsμ, Category.id_comp]
  haveI : IsIso ρ :=
    AlgebraicGeometry.isIso_of_isPullback_of_isIso_of_isNilpotent_ker T' T π hπ hker f f ρ hρf f₀ f₀
      g hg g hg (𝟙 A₀) (by rw [Category.id_comp, hgρ]) (Category.id_comp _)
  refine ⟨m' ≫ inv ρ, ?_, ?_, ?_⟩
  · rw [Category.assoc, (IsIso.inv_comp_eq ρ).mpr hρf.symm, hm'f]
  · have h : pullback.lift e.1 e.1 rfl ≫ m' = e.1 ≫ ρ := by
      rw [hρ, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, hef, Category.id_comp]
    rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [← Category.assoc, hm'μ, Category.assoc, (IsIso.comp_inv_eq ρ).mpr hgρ.symm]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_comp_eq_of_exists_mul_lift
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_comp_eq_of_exists_mul_lift (solution)
