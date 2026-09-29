-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/15c3c23e-c957-5d56-9ebe-7d3338311bba

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc one mul_natural inv one_mul inv_mul_cancel mul"
namespace Shear
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R))

def prG : SchemeHomOver (pullback.fst t g ≫ t) g := ⟨pullback.snd t g, pullback.condition.symm⟩

private def _root_.GoodReductionJacobian.RelativeGroupLaw.Shear.lift (b : SchemeHomOver t g) : SchemeHomOver (pullback.fst t g ≫ t) g :=
  ⟨pullback.fst t g ≫ b.1, by rw [Category.assoc, b.2]⟩

p2m_export "GoodReductionJacobian.RelativeGroupLaw.Shear" "lift"
lemma lift_eq (b : SchemeHomOver t g) :
    lift t b = GoodReductionJacobian.schemeHomOverComp (pullback.fst t g) rfl b := rfl

def shear (b : SchemeHomOver t g) : pullback t g ⟶ pullback t g :=
  pullback.lift (pullback.fst t g) (L.mul (pullback.fst t g ≫ t) (lift t b) (prG t)).1
    (L.mul (pullback.fst t g ≫ t) (lift t b) (prG t)).2.symm

@[scoped simp] lemma shear_fst (b : SchemeHomOver t g) : shear L t b ≫ pullback.fst t g = pullback.fst t g :=
  pullback.lift_fst _ _ _

@[scoped simp] lemma shear_snd (b : SchemeHomOver t g) :
    shear L t b ≫ pullback.snd t g = (L.mul (pullback.fst t g ≫ t) (lift t b) (prG t)).1 :=
  pullback.lift_snd _ _ _

lemma mul_lift (b c : SchemeHomOver t g) :
    L.mul (pullback.fst t g ≫ t) (lift t b) (lift t c) = lift t (L.mul t b c) := by
  rw [lift_eq, lift_eq, lift_eq, ← L.mul_natural]

lemma shear_comp_shear (b c : SchemeHomOver t g) :
    shear L t b ≫ shear L t c = shear L t (L.mul t c b) := by
  have hψ : shear L t b ≫ pullback.fst t g ≫ t = pullback.fst t g ≫ t := by
    rw [← Category.assoc, shear_fst]
  apply pullback.hom_ext
  · simp only [Category.assoc, shear_fst]
  · simp only [Category.assoc, shear_snd]
    have nat := congrArg Subtype.val
      (L.mul_natural (pullback.fst t g ≫ t) (pullback.fst t g ≫ t) (shear L t b) hψ (lift t c) (prG t))
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at nat
    rw [nat]
    have h1 : GoodReductionJacobian.schemeHomOverComp (shear L t b) hψ (lift t c) = lift t c := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, lift, ← Category.assoc, shear_fst]
    have h2 : GoodReductionJacobian.schemeHomOverComp (shear L t b) hψ (prG t) =
        L.mul (pullback.fst t g ≫ t) (lift t b) (prG t) := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, prG, shear_snd]
    rw [h1, h2, ← L.mul_assoc, mul_lift]

lemma shear_one : shear L t (L.one t) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [shear_fst, Category.id_comp]
  · simp only [shear_snd, Category.id_comp]
    have : lift t (L.one t) = L.one (pullback.fst t g ≫ t) := by
      rw [lift_eq, L.one_natural]
    rw [this, L.one_mul]
    rfl

def shearIso (a : SchemeHomOver t g) : pullback t g ≅ pullback t g where
  hom := shear L t a
  inv := shear L t (L.inv t a)
  hom_inv_id := by rw [shear_comp_shear, L.inv_mul_cancel, shear_one]
  inv_hom_id := by rw [shear_comp_shear, L.mul_inv_cancel, shear_one]

end GoodReductionJacobian.RelativeGroupLaw.Shear
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian.RelativeGroupLaw.Shear"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.GoodReductionJacobian.RelativeGroupLaw.Shear"

open GoodReductionJacobian.RelativeGroupLaw.Shear in
theorem solution
    {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    ∃ σ : pullback t g ≅ pullback t g,
      σ.hom ≫ pullback.fst t g = pullback.fst t g ∧
      σ.hom ≫ pullback.snd t g =
        (L.mul (pullback.fst t g ≫ t) ⟨pullback.fst t g ≫ a.1, by rw [Category.assoc, a.2]⟩
          ⟨pullback.snd t g, pullback.condition.symm⟩).1 :=
  ⟨shearIso L t a, shear_fst L t a, shear_snd L t a⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul (solution)
