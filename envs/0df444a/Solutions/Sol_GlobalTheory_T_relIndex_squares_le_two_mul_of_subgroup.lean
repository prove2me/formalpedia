-- Prove2me | solution 1 for GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:19.307797+00:00
-- url     : https://prove2.me/submissions/82a57478-0e44-4ec4-8557-157e26292d93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresLeTwoMulOfSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresLeTwoMulOfSubgroupStatement
import Theorems.Thm_GlobalTheory_QNorm_relIndex_sqs_le_two_mul


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
theorem _root_.solution : ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 → (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 → (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  first | exact @GlobalTheory.QNorm.relIndex_sqs_le_two_mul | exact GlobalTheory.QNorm.relIndex_sqs_le_two_mul | (intros; apply GlobalTheory.QNorm.relIndex_sqs_le_two_mul <;> assumption)
end _root_.GlobalTheory.T
