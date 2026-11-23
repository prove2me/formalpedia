-- Prove2me | solution 1 for GlobalTheory.LagSplit.two_I_imC_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:41.457677+00:00
-- url     : https://prove2.me/submissions/2c2123fb-9eb4-47cf-83e0-83c09c0da15b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_imC_mul_inv
import Theorems.Thm_GlobalTheory_LagSplit_imC_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}
namespace GlobalTheory.LagSplit
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ) * ((2 * I)⁻¹ • (imC τ)⁻¹) = 1 := by
  have h2 : (2 * I : ℂ) ≠ 0 := by simp
  rw [imC_inv hY, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul,
    imC_mul_inv hY]
end GlobalTheory.LagSplit
