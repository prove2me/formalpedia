-- Prove2me | solution 1 for OAI.LaughlinFock.fourHighestNumber_23_21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:27:29.82971+00:00
-- url     : https://prove2.me/submissions/b89c4761-0d26-44bf-b3f5-b6cdfa697a5e

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L022
import Definitions.Def_OAIQ084L024

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_23 : highestFourOccupations 23 = {{0,1,2,21}, {0,1,3,20}, {0,1,4,19}, {0,1,5,18}, {0,1,6,17}, {0,1,7,16}, {0,1,8,15}, {0,1,9,14}, {0,1,10,13}, {0,1,11,12}, {0,2,3,19}, {0,2,4,18}, {0,2,5,17}, {0,2,6,16}, {0,2,7,15}, {0,2,8,14}, {0,2,9,13}, {0,2,10,12}, {0,3,4,17}, {0,3,5,16}, {0,3,6,15}, {0,3,7,14}, {0,3,8,13}, {0,3,9,12}, {0,3,10,11}, {0,4,5,15}, {0,4,6,14}, {0,4,7,13}, {0,4,8,12}, {0,4,9,11}, {0,5,6,13}, {0,5,7,12}, {0,5,8,11}, {0,5,9,10}, {0,6,7,11}, {0,6,8,10}, {0,7,8,9}, {1,2,3,18}, {1,2,4,17}, {1,2,5,16}, {1,2,6,15}, {1,2,7,14}, {1,2,8,13}, {1,2,9,12}, {1,2,10,11}, {1,3,4,16}, {1,3,5,15}, {1,3,6,14}, {1,3,7,13}, {1,3,8,12}, {1,3,9,11}, {1,4,5,14}, {1,4,6,13}, {1,4,7,12}, {1,4,8,11}, {1,4,9,10}, {1,5,6,12}, {1,5,7,11}, {1,5,8,10}, {1,6,7,10}, {1,6,8,9}, {2,3,4,15}, {2,3,5,14}, {2,3,6,13}, {2,3,7,12}, {2,3,8,11}, {2,3,9,10}, {2,4,5,13}, {2,4,6,12}, {2,4,7,11}, {2,4,8,10}, {2,5,6,11}, {2,5,7,10}, {2,5,8,9}, {2,6,7,9}, {3,4,5,12}, {3,4,6,11}, {3,4,7,10}, {3,4,8,9}, {3,5,6,10}, {3,5,7,9}, {3,6,7,8}, {4,5,6,9}, {4,5,7,8}} := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_23_21_oai : ∀ A∈highestFourOccupations 23,
    kernelHighestEntry 23 ⟨⟨21,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_23 21 A := by
  rw [fourOccupations_23]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourHighestNumber_23_21_oai := @OAI.LaughlinFock.fourHighestNumber_23_21_oai
