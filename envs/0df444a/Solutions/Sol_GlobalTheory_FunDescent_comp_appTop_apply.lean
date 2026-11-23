-- Prove2me | solution 1 for GlobalTheory.FunDescent.comp_appTop_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:33.896264+00:00
-- url     : https://prove2.me/submissions/5f24dd44-d84d-4f4d-82b3-1e47f03b3222

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
theorem _root_.solution {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl
end GlobalTheory.FunDescent
