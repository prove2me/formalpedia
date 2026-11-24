-- Prove2me | solution 1 for GlobalTheory.QNorm.relIndex_sqs_sUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:35:11.854954+00:00
-- url     : https://prove2.me/submissions/b31c63e8-d7bc-40a6-be47-1c54fa093814

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Theorems.Thm_GlobalTheory_QNorm_sqs_subgroupOf_self
import Theorems.Thm_GlobalTheory_QNorm_card_sq_eq_one_sUnits
import Theorems.Thm_GlobalTheory_T_finrank_sUnitsNumberField_add_one
import Theorems.Thm_GlobalTheory_T_index_sqs_of_fg
import Theorems.Thm_GlobalTheory_T_sUnitsNumberField_fg


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
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  haveI := GlobalTheory.T.sUnitsNumberField_fg F S
  rw [Subgroup.relIndex, sqs_subgroupOf_self, GlobalTheory.T.index_sqs_of_fg, card_sq_eq_one_sUnits,
    ← GlobalTheory.T.finrank_sUnitsNumberField_add_one F S, pow_succ]
end GlobalTheory.QNorm
