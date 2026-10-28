-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32745
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:35:41.740454+00:00
-- url     : https://prove2.me/submissions/66e1ece5-15a3-4328-8e4f-6b7aefe69f12

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32742

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases001
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

theorem c18 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 1, 3} → False := by
  intro a121 n2
  exact n2 (h.down {0, 1, 2, 3} {0, 1, 3} a121 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases066
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

theorem c25603 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {4, 6, 7} → False := by
  intro a291 a2 a105
  have hc := h.complementary {2, 5, 8, 9} {0, 1, 3} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a2 a105

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases076
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

theorem c31202 (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 3} → False := by
  intro n121
  exact n121 h0

theorem c31204 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 1, 3} → False := by
  classical
  intro n2
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c18 h u0_121 n2

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases108
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

theorem c32317 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a291 a105
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25603 h a291 u0_2 a105

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases136
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

theorem c32745_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 8, 9} → False := by
  classical
  intro a291
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c32317 h h0 a291 u0_105

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32745_oai := @OAI.BorsukNine.FiniteObstruction.c32745_oai
