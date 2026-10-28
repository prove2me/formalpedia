-- Prove2me | solution 1 for OAI.LaughlinFock.fourHighestNumber_21_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:05:48.347646+00:00
-- url     : https://prove2.me/submissions/a005af63-4ee7-4139-911e-5d448311a5f1

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L022
import Definitions.Def_OAIQ084L024

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_21 : highestFourOccupations 21 = {{0,1,2,19}, {0,1,3,18}, {0,1,4,17}, {0,1,5,16}, {0,1,6,15}, {0,1,7,14}, {0,1,8,13}, {0,1,9,12}, {0,1,10,11}, {0,2,3,17}, {0,2,4,16}, {0,2,5,15}, {0,2,6,14}, {0,2,7,13}, {0,2,8,12}, {0,2,9,11}, {0,3,4,15}, {0,3,5,14}, {0,3,6,13}, {0,3,7,12}, {0,3,8,11}, {0,3,9,10}, {0,4,5,13}, {0,4,6,12}, {0,4,7,11}, {0,4,8,10}, {0,5,6,11}, {0,5,7,10}, {0,5,8,9}, {0,6,7,9}, {1,2,3,16}, {1,2,4,15}, {1,2,5,14}, {1,2,6,13}, {1,2,7,12}, {1,2,8,11}, {1,2,9,10}, {1,3,4,14}, {1,3,5,13}, {1,3,6,12}, {1,3,7,11}, {1,3,8,10}, {1,4,5,12}, {1,4,6,11}, {1,4,7,10}, {1,4,8,9}, {1,5,6,10}, {1,5,7,9}, {1,6,7,8}, {2,3,4,13}, {2,3,5,12}, {2,3,6,11}, {2,3,7,10}, {2,3,8,9}, {2,4,5,11}, {2,4,6,10}, {2,4,7,9}, {2,5,6,9}, {2,5,7,8}, {3,4,5,10}, {3,4,6,9}, {3,4,7,8}, {3,5,6,8}, {4,5,6,7}} := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_21_13_oai : ∀ A∈highestFourOccupations 21,
    kernelHighestEntry 21 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_21 13 A := by
  rw [fourOccupations_21]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourHighestNumber_21_13_oai := @OAI.LaughlinFock.fourHighestNumber_21_13_oai
