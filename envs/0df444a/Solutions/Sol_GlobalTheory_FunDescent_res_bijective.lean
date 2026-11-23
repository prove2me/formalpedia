-- Prove2me | solution 1 for GlobalTheory.FunDescent.res_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:34.41909+00:00
-- url     : https://prove2.me/submissions/bba8ae9c-b33f-4148-826a-00da4c2a148d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FunDescent
namespace GlobalTheory.FunDescent
theorem _root_.solution {X : Scheme.{0}} (U : X.Opens) : Function.Bijective (res U).hom := by
  have : res U = U.topIso.inv := by
    simp [res, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  rw [this]
  exact U.topIso.symm.commRingCatIsoToRingEquiv.bijective
end GlobalTheory.FunDescent
