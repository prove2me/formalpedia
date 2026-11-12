-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:43:49.492902+00:00
-- url     : https://prove2.me/submissions/4f22a75b-e4cd-4177-9967-ff5be048f14d

import Mathlib
import Definitions.Def_Q238L025
import Definitions.Def_Q238L028
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchContext_copyData_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCopyTables_locations_pack_s238r

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
attribute [local irreducible] context
attribute [local irreducible] oracle
attribute [local irreducible] classOf
attribute [local irreducible] greenContext
attribute [local irreducible] greenOracle
attribute [local irreducible] ballInput
attribute [local irreducible] copyData
attribute [local irreducible] parts
attribute [local irreducible] origins
attribute [local irreducible] locations
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
local notation "H" => balls δ F s
lemma locations_pack_s238r_oai (hH : ∀ i,(H i).Nonempty) : locations data=BinaryFinSet.table (Completion.CopyGround.location H hH) := by
  rw [locations,copyData_pack_s238r,BinaryCopyTables.locations_pack_s238r _ hH]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r_oai
