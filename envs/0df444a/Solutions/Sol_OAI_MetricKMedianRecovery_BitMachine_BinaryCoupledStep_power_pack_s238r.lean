-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:09.999296+00:00
-- url     : https://prove2.me/submissions/7f612195-9880-473f-a634-59c29e7671a6

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseCount_power_pack_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepPack
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
attribute [local irreducible] BinaryFiniteMachine.continuation 
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
  (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
local notation "xx" => pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s
lemma bf_pack (i : ℕ) : bf i xx=field i (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) := by
  simp only [bf,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,Option.getD_some]
lemma power_pack_s238r_oai : power xx=BinaryRational.encode ((1+v^2)^q) := by
  simp only [power,bf_pack]
  simp only [pack,BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryPhaseCount.power_pack_s238r]
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238r_oai
