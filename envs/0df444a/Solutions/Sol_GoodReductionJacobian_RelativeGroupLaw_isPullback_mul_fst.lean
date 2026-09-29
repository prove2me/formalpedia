-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isPullback_mul_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/43d3a92d-f751-53ac-a490-26d8fc5191cb

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isPullback_mul_fst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace ShearB6

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
  (LG : RelativeGroupLaw R g)

lemma inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x) =
      LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  have hyz : LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = LG.one t' := by
    rw [← LG.mul_natural t t' ψ hψ, LG.inv_mul_cancel, LG.one_natural]
  calc GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x)
      = LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x)) (LG.one t') :=
        (LG.mul_one t' _).symm
    _ = LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x))
          (LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
            (LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x))) := by rw [LG.mul_inv_cancel]
    _ = LG.mul t' (LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x))
          (GoodReductionJacobian.schemeHomOverComp ψ hψ x))
          (LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) := by rw [LG.mul_assoc]
    _ = LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by rw [hyz, LG.one_mul]

end ShearB6

open ShearB6 in
theorem solution
    {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)} (LG : RelativeGroupLaw R g) :
    IsPullback
      (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1
      (pullback.fst g g) g g := by

  set A : SchemeHomOver (pullback.fst g g ≫ g) g := ⟨pullback.fst g g, rfl⟩ with hA
  set B : SchemeHomOver (pullback.fst g g ≫ g) g := ⟨pullback.snd g g, pullback.condition.symm⟩ with hB

  have wφ : pullback.fst g g ≫ g = (LG.mul _ A B).1 ≫ g := (LG.mul _ A B).2.symm
  have wψ : pullback.fst g g ≫ g = (LG.mul _ (LG.inv _ A) B).1 ≫ g := (LG.mul _ (LG.inv _ A) B).2.symm
  let φ : pullback g g ⟶ pullback g g := pullback.lift (pullback.fst g g) (LG.mul _ A B).1 wφ
  let ψ : pullback g g ⟶ pullback g g := pullback.lift (pullback.fst g g) (LG.mul _ (LG.inv _ A) B).1 wψ
  have hφ₁ : φ ≫ pullback.fst g g = pullback.fst g g := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd g g = (LG.mul _ A B).1 := pullback.lift_snd _ _ _
  have hψ₁ : ψ ≫ pullback.fst g g = pullback.fst g g := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd g g = (LG.mul _ (LG.inv _ A) B).1 := pullback.lift_snd _ _ _
  have hφt : φ ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g := by rw [← Category.assoc, hφ₁]
  have hψt : ψ ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g := by rw [← Category.assoc, hψ₁]

  have hφA : GoodReductionJacobian.schemeHomOverComp φ hφt A = A := Subtype.ext hφ₁
  have hφB : GoodReductionJacobian.schemeHomOverComp φ hφt B = LG.mul _ A B := Subtype.ext hφ₂
  have hψA : GoodReductionJacobian.schemeHomOverComp ψ hψt A = A := Subtype.ext hψ₁
  have hψB : GoodReductionJacobian.schemeHomOverComp ψ hψt B = LG.mul _ (LG.inv _ A) B := Subtype.ext hψ₂

  have h1 : φ ≫ (LG.mul _ (LG.inv _ A) B).1 = pullback.snd g g := by
    change (GoodReductionJacobian.schemeHomOverComp φ hφt (LG.mul _ (LG.inv _ A) B)).1 = B.1
    rw [LG.mul_natural _ _ φ hφt, inv_natural LG _ _ φ hφt, hφA, hφB, ← LG.mul_assoc,
      LG.inv_mul_cancel, LG.one_mul]
  have h2 : ψ ≫ (LG.mul _ A B).1 = pullback.snd g g := by
    change (GoodReductionJacobian.schemeHomOverComp ψ hψt (LG.mul _ A B)).1 = B.1
    rw [LG.mul_natural _ _ ψ hψt, hψA, hψB, ← LG.mul_assoc, LG.mul_inv_cancel, LG.one_mul]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hψ₁, hφ₁]
    · rw [Category.id_comp, Category.assoc, hψ₂, h1]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hφ₁, hψ₁]
    · rw [Category.id_comp, Category.assoc, hφ₂, h2]

  exact (IsPullback.of_hasPullback g g).flip.of_iso ⟨ψ, φ, hψφ, hφψ⟩ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact h2.symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact hψ₁.symm) (by simp) (by simp)

end S_GoodReductionJacobian_RelativeGroupLaw_isPullback_mul_fst
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isPullback_mul_fst (solution)
