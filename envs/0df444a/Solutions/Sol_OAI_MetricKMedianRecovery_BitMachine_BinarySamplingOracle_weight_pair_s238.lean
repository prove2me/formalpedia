-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:54.080816+00:00
-- url     : https://prove2.me/submissions/8ef0ae18-3824-485f-b2a5-768ee3672400

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_reference_pair_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma decode_encode (x : ℚ) : decode (encode x)=x := by
  simp only [decode,numerator,denominator,encode,pairBits,extractPrefix_pair,discardPrefix_pair,
    Signed.encode_decode,value_bits,Rat.mkRat_self]

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
lemma weight_pair_s238_oai (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    weight (pairBits (pack δ D S Δ s,w.val.bits))=RationalSampling.clientWeight δ S Δ s w := by
  rw [weight,reference_pair_s238,extractPrefix_pairBits,BinaryRational.decode_encode]
  rfl
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238_oai
