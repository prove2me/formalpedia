-- Prove2me | solution 1 for GlobalTheory.BoxPower.mem_of_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:30.542374+00:00
-- url     : https://prove2.me/submissions/084589d5-7edd-4e1a-93c6-ad336bdd3ad7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic

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
theorem _root_.solution {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) {y : Y} {jN : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN) (i : J) :
    ρ i y ∈ LB.wchart M (φ i) (fun a => jN a i) :=
  Out.GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i) (Out.GeneratorPullback.box_le M pr φ' jN i hy)
end GlobalTheory.BoxPower
