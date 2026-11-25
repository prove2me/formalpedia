-- Prove2me | solution 1 for GlobalTheory.LBLimit.isLB_of_germs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:46.994118+00:00
-- url     : https://prove2.me/submissions/a7a3d985-e329-40e0-8ecf-95cfeae6d34d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRefinementOfIsLimit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.LBLimit
namespace GlobalTheory.LBLimit
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (hc : ∀ y : X, ∃ a, y ∈ L.U a)
    (hg : ∀ a b c (y : X), y ∈ L.U a → y ∈ L.U b → y ∈ L.U c →
      gm (𝟙 X) y _ (L.g a b) * gm (𝟙 X) y _ (L.g b c) = gm (𝟙 X) y _ (L.g a c)) : L.IsLB where
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self a := unit_ext fun y hy => by
    refine (gm_res (𝟙 X) y _ hy _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (hg a a a y hy hy hy)
  cocycle a b c := unit_ext fun y hy => by
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _)
      (gm_res (𝟙 X) y _ hy _))).trans (Eq.trans ?_ (gm_res (𝟙 X) y _ hy _).symm)
    exact hg a b c y hy.1.1 hy.1.2 hy.2
end GlobalTheory.LBLimit
