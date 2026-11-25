-- Prove2me | solution 1 for GlobalTheory.T.exists_normalised_iso_pullback_mul_by_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:21:00.755953+00:00
-- url     : https://prove2.me/submissions/c83c0dd4-dd7d-4525-ba1e-eecfc08c1221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisedIsoPullbackMulByM
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisedIsoPullbackMulByMStatement
import Theorems.Thm_GlobalTheory_KeyKa_exists_normalised_mulPull


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ), ∃ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen ∧ ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) := by
  first | exact @GlobalTheory.KeyKa.exists_normalised_mulPull | exact GlobalTheory.KeyKa.exists_normalised_mulPull | (intros; apply GlobalTheory.KeyKa.exists_normalised_mulPull <;> assumption)
end _root_.GlobalTheory.T
