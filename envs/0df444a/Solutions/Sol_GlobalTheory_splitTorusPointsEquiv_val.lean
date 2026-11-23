-- Prove2me | solution 1 for GlobalTheory.splitTorusPointsEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:47.305254+00:00
-- url     : https://prove2.me/submissions/469d440e-bbb5-48ae-81c9-2f53e1e38ae5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Theorems.Thm_GlobalTheory_SplitTorusPoints_coord_single

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
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S)
    (t : Z ⟶ splitTorus S X) (χ : X) :
    (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val =
      t.left.appTop.hom (charUnit S X χ).val :=
  SplitTorusPoints.coord_single t χ
end GlobalTheory
