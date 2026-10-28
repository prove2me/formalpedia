-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32785
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:40:46.689671+00:00
-- url     : https://prove2.me/submissions/3b97f631-043d-4714-85c1-575328aecd0a

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32720
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32784

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases062
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

theorem c23239 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 5, 8} → T {1, 4, 6} → False := by
  intro a274 a29 a51
  have hc := h.complementary {2, 3, 7, 9} {0, 5, 8} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a51

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases140
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

theorem c32785_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 7, 9} → False := by
  classical
  intro a274
  have u0_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  exact c23239 h a274 u1_29 u0_51

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32785_oai := @OAI.BorsukNine.FiniteObstruction.c32785_oai
