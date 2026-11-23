-- Prove2me | solution 1 for GlobalTheory.LagSplit.imC_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:17.358822+00:00
-- url     : https://prove2.me/submissions/994100c9-4ec0-4cec-a8ea-9f6c53ed6380

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_imC_mul_inv

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
    (imC τ)⁻¹ = ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) :=
  Matrix.inv_eq_right_inv (imC_mul_inv hY)
end GlobalTheory.LagSplit
