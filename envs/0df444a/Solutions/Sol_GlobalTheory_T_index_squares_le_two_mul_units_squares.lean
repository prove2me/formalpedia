-- Prove2me | solution 1 for GlobalTheory.T.index_squares_le_two_mul_units_squares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:38.593716+00:00
-- url     : https://prove2.me/submissions/39a271cc-7945-43e5-bb26-8b1f4c9ba624

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquares
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquaresStatement
import Theorems.Thm_GlobalTheory_QNorm_index_sqs_top_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K), w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 → (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧ (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  first | exact @GlobalTheory.QNorm.index_sqs_top_le | exact GlobalTheory.QNorm.index_sqs_top_le | (intros; apply GlobalTheory.QNorm.index_sqs_top_le <;> assumption)
end _root_.GlobalTheory.T
