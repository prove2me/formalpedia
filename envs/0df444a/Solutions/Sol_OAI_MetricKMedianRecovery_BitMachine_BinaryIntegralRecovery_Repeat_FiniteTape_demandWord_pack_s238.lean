-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:14.4262+00:00
-- url     : https://prove2.me/submissions/faa3e914-4113-4a9c-b510-654cbb035fb2

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K034
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_demandWord_pack_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
attribute [local irreducible] Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
attribute [local irreducible] demandBits
variable {n : ℕ}
lemma demandWord_pack_s238_oai (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g raw : List Bool) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    (demandWord Q (Fair.pack δ D F S Δ P m g raw)).length=Q.eval g.length*Fair.count D Δ m := by
  rw [demandWord,RepeatedAppend.length_copies]
  have hr : (Repeat.rword Q (Fair.pack δ D F S Δ P m g raw)).length=Q.eval g.length := by
    simp only [Repeat.rword,RawUnary.run,List.length_replicate,Repeat.counter,PolynomialCounter.word_length,
      extra,Fair.pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  have hb : (Repeat.bword (Fair.pack δ D F S Δ P m g raw)).length=Fair.count D Δ m := by
    simp only [Repeat.bword,Function.comp_apply,RawUnary.run,List.length_replicate,
      Fair.demandWord_pack_s238 δ D F S Δ P m g raw hm hΔ]
  rw [hr,hb]
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238_oai
