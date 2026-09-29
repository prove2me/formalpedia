-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.translate_comp_schemeNsmul_of_mem_torsionSubset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a52ec325-8f15-5381-a2fd-b5a30d2981b2

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Ws23C0

open GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem mul_mul_mul_comm (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a b x y : SchemeHomOver t f) :
    L.mul t (L.mul t a b) (L.mul t x y) = L.mul t (L.mul t a x) (L.mul t b y) :=
  calc L.mul t (L.mul t a b) (L.mul t x y)
      = L.mul t a (L.mul t b (L.mul t x y)) := L.mul_assoc t a b _
    _ = L.mul t a (L.mul t (L.mul t b x) y) := by rw [← L.mul_assoc t b x y]
    _ = L.mul t a (L.mul t (L.mul t x b) y) := by rw [hc t b x]
    _ = L.mul t a (L.mul t x (L.mul t b y)) := by rw [L.mul_assoc t x b y]
    _ = L.mul t (L.mul t a x) (L.mul t b y) := (L.mul_assoc t a x _).symm

theorem nsmul_mul (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x y : SchemeHomOver t f) :
    L.nsmul t n (L.mul t x y) = L.mul t (L.nsmul t n x) (L.nsmul t n y) := by
  induction n with
  | zero => rw [L.nsmul_zero, L.nsmul_zero, L.nsmul_zero, L.one_mul]
  | succ k ih => rw [L.nsmul_succ, L.nsmul_succ, L.nsmul_succ, ih, mul_mul_mul_comm L hc]

theorem comp_schemeNsmul_eq (n : ℕ) (a : SchemeHomOver f f) :
    a.1 ≫ L.schemeNsmul n = (L.nsmul f n a).1 := by
  have h := L.nsmul_natural f f a.1 a.2 n idPoint
  have ha : schemeHomOverComp a.1 a.2 (idPoint : SchemeHomOver f f) = a := Subtype.ext (Category.comp_id a.1)
  rw [ha] at h
  rw [← h]
  rfl

theorem main (hc : L.IsCommutative) (n : ℕ)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n) :
    L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n := by
  have hψ : f ≫ 𝟙 (Spec (CommRingCat.of R)) = f := Category.comp_id f
  have htor : L.nsmul f n (schemeHomOverComp f hψ x) = L.one f :=
    L.isTorsionPoint_schemeHomOverComp _ _ f hψ n hx
  calc L.translate x ≫ L.schemeNsmul n
      = (L.mul f idPoint (schemeHomOverComp f hψ x)).1 ≫ L.schemeNsmul n := rfl
    _ = (L.nsmul f n (L.mul f idPoint (schemeHomOverComp f hψ x))).1 := comp_schemeNsmul_eq L n _
    _ = (L.mul f (L.nsmul f n idPoint) (L.nsmul f n (schemeHomOverComp f hψ x))).1 := by
        rw [nsmul_mul L hc]
    _ = (L.nsmul f n idPoint).1 := by rw [htor, L.mul_one]
    _ = L.schemeNsmul n := rfl

end Ws23C0

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n) :
    L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n :=
  Ws23C0.main L hc n x hx

end S_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset (solution)
