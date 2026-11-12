-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:41.391207+00:00
-- url     : https://prove2.me/submissions/cbb4c065-10cd-4e22-af74-4d4bbcda3c07

import Mathlib
import Definitions.Def_Q238L029
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_Slices_run_items_s238r

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
lemma slices_labels_s238r_oai {m : ℕ} (U : List (Label (Fin m))) :
    Slices.run (labels U)=Slices.outBits BinaryLabel.encode (CanonicalMergeRefinement.cuts U) :=
  Slices.run_items_s238r BinaryLabel.encode U
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238r_oai
