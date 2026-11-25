-- Prove2me | solution 1 for GlobalTheory.TorusCube.toHom_comp_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:01.126667+00:00
-- url     : https://prove2.me/submissions/796880e6-537b-4b52-ba7e-b389d8a7f429

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusGenCubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_comp


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
open GlobalTheory
open GlobalTheory.TorusCube
open Rosenlicht SplitTorusPoints Geo.Tor
namespace GlobalTheory.TorusCube
theorem _root_.solution {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z W : Over S} (ρ : W ⟶ Z)
    (t : Z ⟶ splitTorus S X) (a : Multiplicative X) :
    (toHom (ρ ≫ t) a).val = ρ.left.appTop.hom (toHom t a).val := by
  change (coord (ρ ≫ t)).hom _ = _
  rw [coord_comp]; rfl
end GlobalTheory.TorusCube
