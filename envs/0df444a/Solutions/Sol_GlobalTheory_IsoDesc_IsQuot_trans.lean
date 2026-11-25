-- Prove2me | solution 1 for GlobalTheory.IsoDesc.IsQuot.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:18.10828+00:00
-- url     : https://prove2.me/submissions/3ad6a9bb-2192-4bee-b4c0-c9595573a88c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}
namespace GlobalTheory.IsoDesc
namespace IsQuot
theorem _root_.solution (hL : L.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    (f : Y ⟶ G) (y : Y) (j j' : M.ι) (i i' : M'.ι) (hj : β (q (f y)) ∈ M.U j) (hj' : β (q (f y)) ∈ M.U j')
    (hi : q (f y) ∈ M'.U i) (hi' : q (f y) ∈ M'.U i') :
    gm f y _ (s j i) = gm ((f ≫ q) ≫ β) y _ (M.g j j') * (gm (f ≫ q) y _ (M'.g i i'))⁻¹ * gm f y _ (s j' i') := by
  obtain ⟨k, hk⟩ := exists_chart hL (f y)
  have a := hw _ f y j j' k k hj hj' hk hk
  rw [hs _ f y j i k hj hi hk, hs _ f y j' i' k hj' hi' hk, hu _ f y i i' k k hi hi' hk hk, ← Category.assoc] at a
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'
end IsQuot
end GlobalTheory.IsoDesc
