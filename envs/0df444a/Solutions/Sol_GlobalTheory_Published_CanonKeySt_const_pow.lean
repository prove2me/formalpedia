-- Prove2me | solution 1 for GlobalTheory.Published.CanonKeySt.const_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:22.995129+00:00
-- url     : https://prove2.me/submissions/2d609957-cc44-45f8-9e3c-d8f1f3422703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_ThetaCharacteristics_ThetaCharZero

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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.CanonKeySt
namespace GlobalTheory.Published.CanonKeySt
theorem _root_.solution (g : ℕ) :
    ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 = (2 * Real.pi : ℂ) ^ (4 * g) := by
  rw [← pow_mul, Nat.mul_comm g 4, pow_mul, pow_mul, mul_pow, Complex.I_pow_four, _root_.mul_one]
end GlobalTheory.Published.CanonKeySt
