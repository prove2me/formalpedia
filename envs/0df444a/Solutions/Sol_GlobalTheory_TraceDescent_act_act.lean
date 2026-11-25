-- Prove2me | solution 1 for GlobalTheory.TraceDescent.act_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:53.523788+00:00
-- url     : https://prove2.me/submissions/fd4bbd38-c8a3-4df8-945e-154d86298a8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Theorems.Thm_GlobalTheory_TraceDescent_coord_act
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_congr
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_pb


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
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish
variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)
namespace GlobalTheory.TraceDescent
theorem _root_.solution {τ σ ρ : Y ⟶ Y} (hτ : τ ≫ f = f) (hσ : σ ≫ f = f) (hρ : ρ ≫ f = f) (H : τ ≫ σ = ρ)
    {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W ≤ σ ⁻¹ᵁ W) (e'' : W ≤ ρ ⁻¹ᵁ W) (s : SecOn (M.pull f) W) :
    act f M hτ e (act f M hσ e' s) = act f M hρ e'' s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_act, coord_act, pb_pb, pb_congr H]
end GlobalTheory.TraceDescent
