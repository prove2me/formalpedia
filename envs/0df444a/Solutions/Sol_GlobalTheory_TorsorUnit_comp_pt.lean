-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.comp_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:02.876263+00:00
-- url     : https://prove2.me/submissions/05428165-9f33-4fff-9cec-9ef0a1371c46

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
theorem _root_.solution (hU : IsAffineOpen U) (f : Z' ⟶ Z) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) :
    f ≫ pt hU θ = pt hU (f.appTop.hom.comp θ) := by
  rw [pt, pt, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc]
  rfl
end GlobalTheory.TorsorUnit
