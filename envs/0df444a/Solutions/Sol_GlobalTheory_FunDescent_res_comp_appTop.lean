-- Prove2me | solution 1 for GlobalTheory.FunDescent.res_comp_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:35.063484+00:00
-- url     : https://prove2.me/submissions/43d35954-5788-45ea-90b0-2be2650bd5e7

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
theorem _root_.solution {X Z : Scheme.{0}} (U : X.Opens) (g : Z ⟶ U.toScheme) (k : Z ⟶ X)
    (e : k = g ≫ U.ι) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    res U ≫ g.appTop = k.appLE U ⊤ h := by
  subst e
  rw [res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
end GlobalTheory.FunDescent
