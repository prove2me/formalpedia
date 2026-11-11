-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:36:48.181451+00:00
-- url     : https://prove2.me/submissions/6895b529-6c6b-46da-98da-580eb6582434

import Mathlib
import Definitions.Def_Q238K021
import Definitions.Def_Q238K025
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchContext_copyData_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCopyTables_locations_pack_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
attribute [local irreducible] remaining
attribute [local irreducible] classOf
attribute [local irreducible] ballInput
attribute [local irreducible] copyData
attribute [local irreducible] origins
attribute [local irreducible] locations
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
local notation "H" => balls δ F s
lemma locations_pack_s238_oai (hH : ∀ i,(H i).Nonempty) : locations data=BinaryFinSet.table (Completion.CopyGround.location H hH) := by
  rw [locations,copyData_pack_s238,BinaryCopyTables.locations_pack_s238 _ hH]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238_oai
