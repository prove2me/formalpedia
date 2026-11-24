-- Prove2me | solution 1 for GlobalTheory.T.index_sqs_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:37.908459+00:00
-- url     : https://prove2.me/submissions/3bef2c6d-574d-45bc-bbc5-3492d469663b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFg
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFgStatement
import Theorems.Thm_GlobalTheory_QNorm_index_sqs_top_of_fg


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
theorem _root_.solution : ∀ (G : Type) [CommGroup G] [Group.FG G], (sqs (⊤ : Subgroup G)).index = 2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  first | exact @GlobalTheory.QNorm.index_sqs_top_of_fg | exact GlobalTheory.QNorm.index_sqs_top_of_fg | (intros; apply GlobalTheory.QNorm.index_sqs_top_of_fg <;> assumption)
end _root_.GlobalTheory.T
