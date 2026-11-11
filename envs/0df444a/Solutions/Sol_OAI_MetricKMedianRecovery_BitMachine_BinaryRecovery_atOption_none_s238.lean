-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:09:14.216356+00:00
-- url     : https://prove2.me/submissions/dc8c56dc-9bd0-48b9-b29f-7a9ad10ae28a

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K040

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryOptionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] run
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s0 s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool)
lemma atOption_none_s238_oai (d : ℕ) : atOption d (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (n:=n) none))=BinaryFinSet.encode S := by
  rw [atOption,discardPrefix_pairBits]
  change (if decide (([]:List Bool)=[]) then src 3 _ else _) = _
  simp only [decide_true,ite_true, if_true]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238_oai
