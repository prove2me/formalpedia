-- Prove2me | solution 1 for GlobalTheory.ThetaRatio.thetaChar_ofRealVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:18:41.065868+00:00
-- url     : https://prove2.me/submissions/16eac05d-b917-4696-8785-a9de2ce590aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RatioSqEqDetJAut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ThetaRatio
namespace GlobalTheory.ThetaRatio
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin g → ℂ) : thetaChar τ (ofRealVec a) (ofRealVec b) z = theta a b z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + ofRealVec a) = shiftVec a l := rfl
  rw [e, thetaTerm, eC]
  congr 1
  ring
end GlobalTheory.ThetaRatio
