-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.comp_translate_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2ce81770-92a5-58ef-8a2b-4499536fba30

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace RP5Sol

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_translate (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    z.1 ≫ L.translate x = (L.mul t z (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x)).1 := by
  let xf : SchemeHomOver f f := ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩
  have h := L.mul_natural f t z.1 z.2 RelativeGroupLaw.idPoint xf
  have h1 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (RelativeGroupLaw.idPoint (f := f)) = z :=
    Subtype.ext (Category.comp_id _)
  have h2 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 xf =
      GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x :=
    Subtype.ext (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, xf, ← Category.assoc, z.2])
  have h' := congrArg Subtype.val h
  rw [h1, h2, GoodReductionJacobian.schemeHomOverComp_coe] at h'
  unfold RelativeGroupLaw.translate
  exact h'

end RP5Sol

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    z.1 ≫ L.translate x = (L.mul t z (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) x)).1 :=
  RP5Sol.comp_translate L t z x

end S_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_translate_eq_mul (solution)
