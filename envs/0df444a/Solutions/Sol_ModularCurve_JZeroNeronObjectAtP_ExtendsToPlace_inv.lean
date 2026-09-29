-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d4a80146-c470-518b-bac5-ec57579d9231

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_inv

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem solution
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    (x : SchemeHomOver (genPt p) f) (hx : ExtendsToPlace A σA x) :
    ExtendsToPlace A σA (L.inv (genPt p) x) := by
  obtain ⟨s, hs⟩ := hx
  refine ⟨L.inv _ s, ?_⟩
  have hs' : schemeHomOverComp (barPt A) hσA s = x := Subtype.ext hs.symm

  have hinv : schemeHomOverComp (barPt A) hσA (L.inv σA s) = L.inv (genPt p) (schemeHomOverComp (barPt A) hσA s) := by
    letI := L.pointGroup (genPt p)
    have h : (schemeHomOverComp (barPt A) hσA (L.inv σA s) : SchemeHomOver (genPt p) f) *
        schemeHomOverComp (barPt A) hσA s = 1 := by
      show L.mul (genPt p) _ _ = L.one (genPt p)
      rw [← L.mul_natural σA (genPt p) (barPt A) hσA, L.inv_mul_cancel, L.one_natural σA (genPt p) (barPt A) hσA]
    exact eq_inv_of_mul_eq_one_left h
  rw [hs'] at hinv
  have := congrArg Subtype.val hinv
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this.symm

end S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_inv
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_inv (solution)
