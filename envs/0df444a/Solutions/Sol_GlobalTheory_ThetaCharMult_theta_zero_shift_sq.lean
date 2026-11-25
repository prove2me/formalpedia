-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.theta_zero_shift_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:42.776278+00:00
-- url     : https://prove2.me/submissions/4a711813-a15f-45ba-be5e-4afa6490cf37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_PTheta_thetaRealTransl_holds


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
theorem _root_.solution (a b : Fin g → ℝ) (z : Fin g → ℂ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ.IsSymm) :
    theta (halfVec 0) (halfVec 0) (z + τ *ᵥ ofRealVec a + ofRealVec b) τ ^ 2 =
      eC (2 * (-(ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a)) / 2 - ofRealVec a ⬝ᵥ (z + ofRealVec b))) *
        theta a b z τ ^ 2 := by
  have h0 : halfVec (0 : Fin g → ℤ) = 0 := by ext i; simp [halfVec]
  have h00 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  rw [h0, thetaRealTransl_holds (Fin g) 0 0 a b z τ hτ, mul_pow, eC_pow, h00, zero_add, zero_add,
    add_zero]
  norm_num
end GlobalTheory.ThetaCharMult
