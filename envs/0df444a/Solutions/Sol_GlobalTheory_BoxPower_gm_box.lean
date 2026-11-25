-- Prove2me | solution 1 for GlobalTheory.BoxPower.gm_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:02.566558+00:00
-- url     : https://prove2.me/submissions/100e7857-25e3-40a4-9a05-51e91aef6d81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic
import Theorems.Thm_GlobalTheory_BoxPower_mem_of_box
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) {y : Y} {jN : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN) :
    gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN)
      ((Out.GeneratorPullback.boxGen M pr φ' ε (fun i => Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jN) =
      ∏ i, gm (ρ i) y (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) := by
  refine (map_prod (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN))
    (fun i => res (Out.GeneratorPullback.box_le M pr φ' jN i)
      ((Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => jN a i))) Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  refine (gm_res (𝟙 Y) y (Out.GeneratorPullback.box_le M pr φ' jN i) hy _).trans ?_
  refine (gm_res (𝟙 Y) y (Out.GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i))
    (Out.GeneratorPullback.box_le M pr φ' jN i hy) _).trans ?_
  refine (gm_pull (𝟙 Y) (ρ i) y _ (mem_of_box hψ hy i) _).trans ?_
  rw [Category.id_comp]
end GlobalTheory.BoxPower
