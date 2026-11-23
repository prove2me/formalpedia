-- Prove2me | solution 1 for GlobalTheory.WeightGen.gm_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:36.433156+00:00
-- url     : https://prove2.me/submissions/79de6b85-d259-4a69-afe0-584a3b755362

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_gm_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div


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
theorem _root_.solution {L M : LB B} {w : LB.Iso L M} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : M.ι} {k k' : L.ι} (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') (hk : r z ∈ L.U k)
    (hk' : r z ∈ L.U k') :
    gm r z (M.U j ⊓ L.U k) (w.s (j, k)) = gm r z _ (M.g j j') * (gm r z _ (L.g k k'))⁻¹ *
      gm r z (M.U j' ⊓ L.U k') (w.s (j', k')) := by
  have := gm_gen hw r z (j := (j, k)) (j' := (j', k')) ⟨hj, hk⟩ ⟨hj', hk'⟩
  exact this.trans (congrArg (· * _) (gm_div L M r z (j, k) (j', k') ⟨⟨hj, hk⟩, hj', hk'⟩))
end GlobalTheory.WeightGen
