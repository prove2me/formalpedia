-- Prove2me | solution 1 for GlobalTheory.BoxPower.trF_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:14.784911+00:00
-- url     : https://prove2.me/submissions/25b7fb9f-98d4-4c9c-950d-4ab930005923

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BoxPower
variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {J K : Type} [Fintype J] [Fintype K]
namespace GlobalTheory.BoxPower
theorem _root_.solution {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) {y : Y} {jN jN' : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN)
    (hy' : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN') :
    trF (L := LB.LinComb M pr (fun _ => 1)) φ' ε (𝟙 Y) y jN jN' =
      ∏ i, trF (φ i) ε (ρ i) y (fun a => jN a i) (fun a => jN' a i) := by
  unfold trF
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_zpow]
  refine congrArg (· ^ ε a) ?_
  refine (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a) (Set.mem_iInter.1 hy a)
    (Set.mem_iInter.1 hy' a)).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [zpow_one, Category.id_comp, hψ]
end GlobalTheory.BoxPower
