-- Prove2me | solution 1 for GlobalTheory.HolZeros.IsLevel.zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:28.765475+00:00
-- url     : https://prove2.me/submissions/37301421-9d5b-4f0c-b9cb-0ed2a0355f0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically

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
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open GlobalTheory GlobalTheory.HolZeros
namespace GlobalTheory.HolZeros
namespace IsLevel
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {n : ℕ}
    {F : (Fin g → ℂ) → ℂ} (h : IsLevel τ a b n F) (m m' : Fin g → ℤ) (z : Fin g → ℂ) :
    F (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (m' i : ℂ)))) = 0 ↔ F z = 0 := by
  rw [h.2, mul_eq_zero, or_iff_right (pow_ne_zero _ (Complex.exp_ne_zero _))]
end IsLevel
end GlobalTheory.HolZeros
