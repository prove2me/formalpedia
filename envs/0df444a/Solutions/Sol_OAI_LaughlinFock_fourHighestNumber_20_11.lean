-- Prove2me | solution 1 for OAI.LaughlinFock.fourHighestNumber_20_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:54:44.89689+00:00
-- url     : https://prove2.me/submissions/2211a88a-13df-4022-be11-fd720d9b7dfd

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L022
import Definitions.Def_OAIQ084L024

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20Data
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourOccupations_20 : highestFourOccupations 20 = {{0,1,2,18}, {0,1,3,17}, {0,1,4,16}, {0,1,5,15}, {0,1,6,14}, {0,1,7,13}, {0,1,8,12}, {0,1,9,11}, {0,2,3,16}, {0,2,4,15}, {0,2,5,14}, {0,2,6,13}, {0,2,7,12}, {0,2,8,11}, {0,2,9,10}, {0,3,4,14}, {0,3,5,13}, {0,3,6,12}, {0,3,7,11}, {0,3,8,10}, {0,4,5,12}, {0,4,6,11}, {0,4,7,10}, {0,4,8,9}, {0,5,6,10}, {0,5,7,9}, {0,6,7,8}, {1,2,3,15}, {1,2,4,14}, {1,2,5,13}, {1,2,6,12}, {1,2,7,11}, {1,2,8,10}, {1,3,4,13}, {1,3,5,12}, {1,3,6,11}, {1,3,7,10}, {1,3,8,9}, {1,4,5,11}, {1,4,6,10}, {1,4,7,9}, {1,5,6,9}, {1,5,7,8}, {2,3,4,12}, {2,3,5,11}, {2,3,6,10}, {2,3,7,9}, {2,4,5,10}, {2,4,6,9}, {2,4,7,8}, {2,5,6,8}, {3,4,5,9}, {3,4,6,8}, {3,5,6,7}} := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourHighestNumber_20_11_oai : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 11 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourHighestNumber_20_11_oai := @OAI.LaughlinFock.fourHighestNumber_20_11_oai
