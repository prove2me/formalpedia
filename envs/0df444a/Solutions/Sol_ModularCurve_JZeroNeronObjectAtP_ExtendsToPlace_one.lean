-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3b188639-ee62-5970-a671-03459740dd01

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem solution
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f) :
    ExtendsToPlace A σA (L.one (genPt p)) := by
  refine ⟨L.one σA, ?_⟩
  have := congrArg Subtype.val (L.one_natural σA (genPt p) (barPt A) hσA)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this.symm

end S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_one
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_one (solution)
