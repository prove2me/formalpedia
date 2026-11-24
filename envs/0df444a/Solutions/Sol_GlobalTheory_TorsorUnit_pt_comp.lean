-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.pt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:46.643559+00:00
-- url     : https://prove2.me/submissions/b7c48482-e9ff-4435-8131-cba69da55477

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory.TorsorUnit
variable {Y Z Z' : Scheme.{0}} {U : Y.Opens}
namespace GlobalTheory.TorsorUnit
theorem _root_.solution {B : Scheme.{0}} {V : B.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : Y ⟶ B) (e : U ≤ q ⁻¹ᵁ V) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) :
    pt hU θ ≫ q = pt hV (θ.comp (q.appLE V U e).hom) := by
  rw [pt, pt, Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec q hU e,
    ← Spec.map_comp_assoc]
  rfl
end GlobalTheory.TorsorUnit
