-- Prove2me | solution 1 for GlobalTheory.Published.CanonKeySt.thetaChar_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:26.623299+00:00
-- url     : https://prove2.me/submissions/8665719d-15d0-4b00-8dd8-8e9d025d110a

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
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    thetaChar τ 0 0 z = ∑' n : Fin g → ℤ,
      Complex.exp (Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec fun i => (n i : ℂ)) +
        2 * Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z)) := by
  simp only [thetaChar, add_zero]
end GlobalTheory.Published.CanonKeySt
