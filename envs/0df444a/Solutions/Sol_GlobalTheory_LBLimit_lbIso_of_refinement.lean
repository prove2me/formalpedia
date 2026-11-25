-- Prove2me | solution 1 for GlobalTheory.LBLimit.lbIso_of_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:55:08.419259+00:00
-- url     : https://prove2.me/submissions/7d888092-6984-4e87-b933-8cbaa2ff27bf

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
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
theorem _root_.solution {X : Scheme.{0}} (L N : LB X) (hL : L.IsLB) (e : N.ι → L.ι)
    (he : ∀ a, N.U a ≤ L.U (e a))
    (hg : ∀ a b (y : X), y ∈ N.U a → y ∈ N.U b →
      gm (𝟙 X) y _ (N.g a b) = gm (𝟙 X) y _ (L.g (e a) (e b))) : LBIso L N := by
  have le : ∀ p : N.ι × L.ι, (LB.div N L).U p ≤ L.U (e p.1) ⊓ L.U p.2 :=
    fun p y hy => ⟨he _ hy.1, hy.2⟩
  refine ⟨⟨fun p => res (le p) (L.g (e p.1) p.2)⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L N (𝟙 X) y p q hy)
      ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y _ hy.2 _)))).symm)
  rw [hg p.1 q.1 y hy.1.1 hy.2.1, mul_right_comm,
    gm_cocycle hL (𝟙 X) y (he _ hy.1.1) (he _ hy.2.1) hy.2.2,
    ← gm_cocycle hL (𝟙 X) y (he _ hy.1.1) hy.1.2 hy.2.2, mul_inv_cancel_right]
end GlobalTheory.LBLimit
