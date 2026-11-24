-- Prove2me | solution 1 for GlobalTheory.WeightVal.gs_chiP_whisker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:38.582871+00:00
-- url     : https://prove2.me/submissions/2253d920-4252-4fb4-8de2-0938214a5bfd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.WeightVal
namespace GlobalTheory.WeightVal
theorem _root_.solution {S : Scheme.{0}} (X : Type) [AddCommGroup X] {Z Y : Over S} (x : Z ⟶ Y) (χ : X)
    (w : (splitTorus S X ⊗ Z).left) :
    gs (splitTorus S X ◁ x).left w ⊤ (TorusInj.chiP X Y χ) = gs (𝟙 _) w ⊤ (TorusInj.chiP X Z χ) := by
  refine (gs_pull (splitTorus S X ◁ x).left (fst (splitTorus S X) Y).left w ⊤ trivial _).trans
    (Eq.trans ?_ (gs_pull (𝟙 _) (fst (splitTorus S X) Z).left w ⊤ trivial _).symm)
  rw [Category.id_comp, ← Over.comp_left, whiskerLeft_fst]
end GlobalTheory.WeightVal
