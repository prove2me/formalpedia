-- Prove2me | solution 1 for GlobalTheory.WeilCube.exists_gen_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:55.096391+00:00
-- url     : https://prove2.me/submissions/d63258ca-858c-4814-b936-ca3c539ec2b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
namespace GlobalTheory.WeilCube
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (i : K → L.ι) (h : ∀ y, y ∈ LB.wchart L φ i) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ i := fun j => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j i)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j i)) =
      trF φ ε (𝟙 Y) y j i := fun j hj => (gm_res _ y _ hj _).trans (gm_linComb L φ ε _ y j i hj (h y))
  refine ((gm_res _ y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy _).trans (v j' hy.2)))).symm)
  exact (trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h y)).symm
end GlobalTheory.WeilCube
