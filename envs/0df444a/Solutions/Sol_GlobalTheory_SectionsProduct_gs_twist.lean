-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.gs_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:54.028827+00:00
-- url     : https://prove2.me/submissions/219fa315-c400-4afc-8d3d-e4b1b0bb6b5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_g

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
namespace GlobalTheory.SectionsProduct
theorem _root_.solution (i : Y ⟶ S) (φ : K → (Y ⟶ B)) (ε : K → ℤ) {U U' : Y.Opens} {j j' : K → L.ι}
    (hU : U ≤ LB.wchart L φ j) (hU' : U' ≤ LB.wchart L φ j') (r : T ⟶ Y) (z : T) (hz : r z ∈ U ⊓ U') (a : Fn i U') :
    gs r z (U ⊓ U') (twist i φ ε hU hU' a) = (trF φ ε r z j j').val * gs r z U' a :=
  (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z _ hz _).trans (gs_g φ ε r z (hU hz.1) (hU' hz.2))) (gs_res r z _ hz _))
end GlobalTheory.SectionsProduct
