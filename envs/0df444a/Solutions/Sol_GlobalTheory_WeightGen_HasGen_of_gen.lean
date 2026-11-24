-- Prove2me | solution 1 for GlobalTheory.WeightGen.HasGen.of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:54.65388+00:00
-- url     : https://prove2.me/submissions/76a56f30-4fb5-49d1-816f-a463d8c5f2fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_pt_eq
import Theorems.Thm_GlobalTheory_WeightGen_gm_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


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
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}
namespace GlobalTheory.WeightGen
namespace HasGen
theorem _root_.solution (h : a ≫ q = p ≫ q) {N : LB B} (t : LB.Gen N) (ht : t.IsGen) :
    HasGen q a p N (fun _ _ _ => 1) := by
  refine ⟨fun j => (pullU q _ (t.s j))⁻¹, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · rw [map_inv, map_inv, gm_pull r q z _ h₁, gm_pull r q z _ h₂, gm_gen ht (r ≫ q) z h₁ h₂,
      mul_inv, mul_inv_cancel_left]
  · rw [map_inv, map_inv, gm_pull (r ≫ p) q z _ h₁,
      gm_pull (r ≫ a) q z _ ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _), _root_.one_mul,
      Category.assoc, Category.assoc, h]
end HasGen
end GlobalTheory.WeightGen
