-- Prove2me | solution 1 for GlobalTheory.SplitTorusPoints.coord_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:44.81484+00:00
-- url     : https://prove2.me/submissions/549f4d73-bba5-4b8b-9882-addbc92e7f27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val


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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SplitTorusPoints
open Rosenlicht
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}
namespace GlobalTheory.SplitTorusPoints
theorem _root_.solution (t : Z ⟶ splitTorus S X) (x : X) :
    (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (charUnit S X x).val := by
  rw [TorusInj.charUnit_val, coord, Scheme.Hom.comp_appTop]
  have : (TorusInj.tFst (S := S) X).appLE ⊤ ⊤ (TorusInj.tle _) = (torusFst S X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this]
  rfl
end GlobalTheory.SplitTorusPoints
