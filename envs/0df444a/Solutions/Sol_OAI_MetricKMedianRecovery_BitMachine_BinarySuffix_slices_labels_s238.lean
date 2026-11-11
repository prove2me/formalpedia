-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:57.725075+00:00
-- url     : https://prove2.me/submissions/2b67da5f-a8f8-4631-93d3-bcd3027c6db1

import Mathlib
import Definitions.Def_Q238K030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_Slices_run_items_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
lemma slices_labels_s238_oai {m : ℕ} (U : List (Label (Fin m))) :
    Slices.run (labels U)=Slices.outBits BinaryLabel.encode (CanonicalMergeRefinement.cuts U) :=
  Slices.run_items_s238 BinaryLabel.encode U
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238_oai
