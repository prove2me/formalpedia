-- Prove2me | solution 1 for IntMul.Kappa.R6.Leaf.ail6s_of_fine
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:33:53.537292+00:00
-- url     : https://prove2.me/submissions/a8d6cedf-3154-484c-924a-9dcc098bea3e

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_AIL6s_of_axis
import Theorems.Thm_J6Seg_Ax_axisUA6_of
import Theorems.Thm_J6Seg_pipeGBA6_all
import Theorems.Thm_J6A_AS_aStepNeed6_all
import Theorems.Thm_J6Seg_AC_aKerNeedA6_all
import Theorems.Thm_J6Seg_ATab_preA6

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.Ax J6Seg.AC J6Seg.ATab J6A.AS
open IntMul.Kappa.R6
open NLogN

/-- `AIL6s` under the `LineNeed6` table hypotheses reduces to the published
assemblers `axisUA6_of` and `AIL6s_of_axis`, with `PipeGBA6` from `pipeGBA6_all`
and the remaining A-side leaves `aStepNeed6_all`, `aKerNeedA6_all`, and `preA6`. -/
theorem solution (P : Prm) (hP : P.Ok) (tab : Fin 1 → IStmt HS 1)
    (hSw : IL.SwapNeedτ tab P.τ) (hRow : IL2.RowUCP 576 P.τ tab) (hFU : FineU6 tab) :
    AIL6s P tab :=
  AIL6s_of_axis P hP tab
    (axisUA6_of P hP (aStepNeed6_all P hP) (aKerNeedA6_all P hP) tab hFU
      (preA6 P hP 8 16 17 40 tab))
    (pipeGBA6_all P hP)
