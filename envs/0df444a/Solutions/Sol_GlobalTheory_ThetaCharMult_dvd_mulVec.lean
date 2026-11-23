-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.dvd_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:29.860259+00:00
-- url     : https://prove2.me/submissions/286f6be9-9691-41e9-9c5c-b94280d99b98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaCharMult
variable {g : ℕ}
namespace GlobalTheory.ThetaCharMult
theorem _root_.solution {M : Matrix (Fin g) (Fin g) ℤ} {k : ℤ} (h : ∀ i j, k ∣ M i j) (v : Fin g → ℤ)
    (i : Fin g) : k ∣ (M *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => (h i j).mul_right _
end GlobalTheory.ThetaCharMult
