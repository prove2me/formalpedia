-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b91cd40c-b94c-590d-a376-70498172226e

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem solution
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    (x y : SchemeHomOver (genPt p) f)
    (hx : ExtendsToPlace A σA x) (hy : ExtendsToPlace A σA y) :
    ExtendsToPlace A σA (L.mul (genPt p) x y) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  refine ⟨L.mul _ s t, ?_⟩
  have hs' : schemeHomOverComp (barPt A) hσA s = x := Subtype.ext hs.symm
  have ht' : schemeHomOverComp (barPt A) hσA t = y := Subtype.ext ht.symm
  have h := L.mul_natural σA (genPt p) (barPt A) hσA s t
  rw [hs', ht'] at h
  have := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this.symm

end S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_mul
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_mul (solution)
