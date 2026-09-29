-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7d586325-bc88-5854-850b-cdeceaa2a50c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace LawTransportBody

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
  (e : A ≅ A') (he : e.hom ≫ f' = f)

include he in
theorem he' : e.inv ≫ f = f' := by rw [← he, Iso.inv_hom_id_assoc]

def toA {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x' : SchemeHomOver t f') : SchemeHomOver t f :=
  ⟨x'.1 ≫ e.inv, by rw [Category.assoc, he' e he, x'.2]⟩

def toA' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩

@[scoped simp] theorem toA_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x' : SchemeHomOver t f') :
    (toA e he x').1 = x'.1 ≫ e.inv := rfl
@[scoped simp] theorem toA'_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) :
    (toA' e he x).1 = x.1 ≫ e.hom := rfl

@[scoped simp] theorem toA_toA' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f) :
    toA e he (toA' e he x) = x := Subtype.ext (by simp)
@[scoped simp] theorem toA'_toA {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x' : SchemeHomOver t f') :
    toA' e he (toA e he x') = x' := Subtype.ext (by simp)

theorem toA_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x' : SchemeHomOver t f') :
    toA e he (schemeHomOverComp ψ hψ x') = schemeHomOverComp ψ hψ (toA e he x') :=
  Subtype.ext (by simp [schemeHomOverComp_coe])

theorem toA'_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    toA' e he (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (toA' e he x) :=
  Subtype.ext (by simp [schemeHomOverComp_coe])

def transport (L : RelativeGroupLaw R f) : RelativeGroupLaw R f' where
  mul t x' y' := toA' e he (L.mul t (toA e he x') (toA e he y'))
  one t := toA' e he (L.one t)
  inv t x' := toA' e he (L.inv t (toA e he x'))
  mul_assoc t x y z := by simp only [toA_toA', L.mul_assoc]
  one_mul t x := by simp only [toA_toA', L.one_mul, toA'_toA]
  mul_one t x := by simp only [toA_toA', L.mul_one, toA'_toA]
  inv_mul_cancel t x := by simp only [toA_toA', L.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    rw [← toA'_comp, L.mul_natural, toA_comp, toA_comp]

end LawTransportBody
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso.LawTransportBody"

open LawTransportBody in

theorem solution
    {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (L : RelativeGroupLaw R f) :
    ∃ L' : RelativeGroupLaw R f',
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1 =
          (L.mul t x y).1 ≫ e.hom) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (L'.one t).1 = (L.one t).1 ≫ e.hom) := by
  refine ⟨transport e he L, fun t x y => ?_, fun t => rfl⟩
  show (toA' e he (L.mul t (toA e he ⟨x.1 ≫ e.hom, _⟩) (toA e he ⟨y.1 ≫ e.hom, _⟩))).1 = (L.mul t x y).1 ≫ e.hom
  have hx : toA e he ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ = x := toA_toA' e he x
  have hy : toA e he ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩ = y := toA_toA' e he y
  rw [hx, hy]
  rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso (solution)
