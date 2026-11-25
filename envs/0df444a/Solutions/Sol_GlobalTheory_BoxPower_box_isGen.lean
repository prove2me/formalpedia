-- Prove2me | solution 1 for GlobalTheory.BoxPower.box_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:29:31.107818+00:00
-- url     : https://prove2.me/submissions/4baecb1b-0d76-4091-a442-ebc774580a83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic
import Theorems.Thm_GlobalTheory_BoxPower_mem_of_box
import Theorems.Thm_GlobalTheory_BoxPower_gm_box
import Theorems.Thm_GlobalTheory_BoxPower_trF_box
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm


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
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    (Out.GeneratorPullback.boxGen M pr φ' ε (fun i => Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).IsGen := by
  refine isGen_of_gm _ fun y jN jN' hy hy' => ?_
  refine (gm_box hψ t hy).trans (Eq.trans ?_ (congrArg₂ (· * ·) (trF_box hψ hy hy') (gm_box hψ t hy')).symm)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (ρ i) y (mem_of_box hψ hy i) (mem_of_box hψ hy' i)
end GlobalTheory.BoxPower
