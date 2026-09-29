-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.ext_of_forall_algebraicClosure_point_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f44741c6-0c7b-5d41-9614-465c5c675b2a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace RelativeGroupLawExtAux

theorem ext_of_mul_eq {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    (L₁ L₂ : RelativeGroupLaw R f)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L₁.mul t x y = L₂.mul t x y) : L₁ = L₂ := by
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), L₁.one t = L₂.one t := by
    intro T t
    calc L₁.one t = L₂.mul t (L₁.one t) (L₂.one t) := (L₂.mul_one t _).symm
      _ = L₁.mul t (L₁.one t) (L₂.one t) := (h t _ _).symm
      _ = L₂.one t := L₁.one_mul t _
  have hinv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      L₁.inv t x = L₂.inv t x := by
    intro T t x
    calc L₁.inv t x = L₁.mul t (L₁.inv t x) (L₁.one t) := (L₁.mul_one t _).symm
      _ = L₁.mul t (L₁.inv t x) (L₂.mul t x (L₂.inv t x)) := by rw [L₂.mul_inv_cancel, hone]
      _ = L₁.mul t (L₁.inv t x) (L₁.mul t x (L₂.inv t x)) := by rw [h t x]
      _ = L₁.mul t (L₁.mul t (L₁.inv t x) x) (L₂.inv t x) := (L₁.mul_assoc t _ _ _).symm
      _ = L₂.inv t x := by rw [L₁.inv_mul_cancel, L₁.one_mul]
  rcases L₁ with ⟨m₁, o₁, i₁, _, _, _, _, _⟩
  rcases L₂ with ⟨m₂, o₂, i₂, _, _, _, _, _⟩
  have hm : @m₁ = @m₂ := by
    funext T t x y; exact h t x y
  have ho : @o₁ = @o₂ := by
    funext T t; exact hone t
  have hi : @i₁ = @i₂ := by
    funext T t x; exact hinv t x
  subst hm ho hi
  rfl

theorem mul_eq_schemeHomOverComp_lift {R : Type u} [CommRing R] {G : Scheme.{u}}
    {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    L.mul t x y =
      GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm))
        (by rw [pullback.lift_fst_assoc, x.2])
        (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩) := by
  rw [L.mul_natural]
  congr 1
  · exact Subtype.ext (pullback.lift_fst _ _ _).symm
  · exact Subtype.ext (pullback.lift_snd _ _ _).symm

theorem isReduced_pullback_of_smooth {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of R))
    [Smooth f] : IsReduced (pullback f f) := by
  haveI : IsReduced (pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    AlgebraicGeometry.isReduced_of_smooth_of_field
      (pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  exact AlgebraicGeometry.isReduced_of_flat_of_isReduced_pullback_of_isFractionRing K (pullback.fst f f ≫ f)

end RelativeGroupLawExtAux

open RelativeGroupLawExtAux in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar]
    [IsScalarTower R K Kbar]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    [Smooth f] [IsSeparated f]
    (L₁ L₂ : RelativeGroupLaw R f)
    (hmul : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) f,
      L₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) x y =
        L₂.mul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) x y) :
    L₁ = L₂ := by
  apply ext_of_mul_eq
  intro T t x y
  have key : L₁.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      L₂.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩ := by
    haveI : IsReduced (pullback f f) := isReduced_pullback_of_smooth K f
    apply AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat K Kbar
    intro z
    have h₁ := congrArg Subtype.val
      (L₁.mul_natural (pullback.fst f f ≫ f) _ z.1 z.2 ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    have h₂ := congrArg Subtype.val
      (L₂.mul_natural (pullback.fst f f ≫ f) _ z.1 z.2 ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h₁ h₂
    rw [h₁, h₂, hmul]
  rw [mul_eq_schemeHomOverComp_lift L₁, mul_eq_schemeHomOverComp_lift L₂, key]

end S_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq (solution)
