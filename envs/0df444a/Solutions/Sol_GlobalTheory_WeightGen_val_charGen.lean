-- Prove2me | solution 1 for GlobalTheory.WeightGen.val_charGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:46.800196+00:00
-- url     : https://prove2.me/submissions/9e89f4a7-248d-4897-934b-34906886e107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_gm_res_pull_top

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
open GlobalTheory GlobalTheory.WeightGen
namespace GlobalTheory.WeightGen
theorem _root_.solution {S Y Z : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) (L : LB Y) (χ : X)
    (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) (J : (Z ⟶ Y) → L.ι) :
    val (charGen X G L χ) r z J = gm (r ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ) :=
  gm_res_pull_top r z (fst (splitTorus S X) G).left
    (V := LB.wchart L (PEmpty.elim : PEmpty → (_ ⟶ Y)) fun k => J (r ≫ k.elim))
    (Set.mem_iInter.2 fun k => k.elim) (fun _ _ => trivial) _
end GlobalTheory.WeightGen
