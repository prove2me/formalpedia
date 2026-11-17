-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_unit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:47.557248+00:00
-- url     : https://prove2.me/submissions/e3fc5015-379a-40c0-a3f2-f66cb3cc0fc8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

/-- The identity section lies in the zero division fibre. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ (η : SchemeHomOver (𝟙 _) (Sigma.desc g))
        (z : SchemeHomOver (𝟙 _) (g 0)),
      η.1 = z.1 ≫ Sigma.ι X 0 ∧
      z.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) (0 : ZMod 71).val S).1 =
        (L.one (𝟙 _)).1 := by
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  have h : (L.one (𝟙 _)).1 ≫ L.schemeNsmul 71 =
      𝟙 _ ≫ (L.nsmul (𝟙 _) (0 : ZMod 71).val S).1 := by
    rw [← L.coe_nsmul_eq_comp_schemeNsmul, L.nsmul_unit]
    simp
  let z : SchemeHomOver (𝟙 _) (g 0) :=
    ⟨pullback.lift (L.one (𝟙 _)).1 (𝟙 _) h, by simp only [g, pullback.lift_snd]⟩
  refine ⟨⟨z.1 ≫ Sigma.ι X 0, ?_⟩, z, rfl, ?_⟩
  · change z.1 ≫ Sigma.ι X 0 ≫ Sigma.desc g = 𝟙 _
    rw [Sigma.ι_desc]
    exact z.2
  · exact pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativeGroupLaw
