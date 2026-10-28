-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32800
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:44:10.970814+00:00
-- url     : https://prove2.me/submissions/53538038-fe0d-4519-a6df-01044738fc63

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32795

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases015
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1393 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {3, 5, 8} → False := by
  intro a309 n93
  exact n93 (h.down {3, 5, 7, 8} {3, 5, 8} a309 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases142
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32800_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → False := by
  classical
  intro a309
  have u0_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  exact c1393 h a309 u0_93

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32800_oai := @OAI.BorsukNine.FiniteObstruction.c32800_oai
