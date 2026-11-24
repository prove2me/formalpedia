-- Prove2me | solution 1 for GlobalTheory.LagSplit.perProj_secH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:50:16.706852+00:00
-- url     : https://prove2.me/submissions/e95e244c-578e-4753-8ba0-c12af2a43289

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_perProj_elim
import Theorems.Thm_GlobalTheory_LagSplit_secH_apply
import Theorems.Thm_GlobalTheory_LagSplit_sub_map_star
import Theorems.Thm_GlobalTheory_LagSplit_two_I_imC_mul_inv

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
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (z : Fin g → ℂ) : perProj τ (secH τ z) = z := by
  rw [secH_apply, perProj_elim, neg_add_eq_sub, ← Matrix.sub_mulVec, sub_map_star,
    Matrix.mulVec_mulVec, two_I_imC_mul_inv hY, Matrix.one_mulVec]
end GlobalTheory.LagSplit
