-- Prove2me | solution 1 for GlobalTheory.FunDescent.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:10.829124+00:00
-- url     : https://prove2.me/submissions/abc746bf-fee5-42e6-a09c-ee42f96f5faf

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
theorem _root_.solution {Z : Scheme.{0}} {g h : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ))}
    (e : g.appTop.hom coord = h.appTop.hom coord) : g = h := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext'
  · exact RingHom.ext_int _ _
  · exact e
end GlobalTheory.FunDescent
