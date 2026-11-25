-- Prove2me | solution 1 for GlobalTheory.SimilUnit.IsVal.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:49.864321+00:00
-- url     : https://prove2.me/submissions/e12d3841-9612-45ae-b4b6-399cfb7b3d8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisingUnitSimilitudeOrigin

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
noncomputable section
open GlobalTheory GlobalTheory.SimilUnit
variable {X Y Y' : Scheme.{0}} (L : LB X)
variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}
namespace GlobalTheory.SimilUnit
namespace IsVal
theorem _root_.solution (a : IsVal L F v) (n : ℕ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsVal.one
  | succ n ih => simpa only [pow_succ] using ih.mul a
end IsVal
end GlobalTheory.SimilUnit
