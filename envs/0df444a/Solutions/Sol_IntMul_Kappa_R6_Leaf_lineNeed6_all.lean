-- Prove2me | solution 1 for IntMul.Kappa.R6.Leaf.lineNeed6_all
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:23:56.741583+00:00
-- url     : https://prove2.me/submissions/ae8c13b3-5790-480c-a194-3d221249ddfc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs63
import Theorems.Thm_J6Seg_lineBody6_top
import Theorems.Thm_J6Seg_pipeDisc6_all
import Theorems.Thm_IntMul_Kappa_R6_Leaf_ail6s_of_fine
import Theorems.Thm_IntMul_Kappa_R6_Leaf_axisU6_of_fine

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg
open IntMul.Kappa.R6
open IntMul.Kappa.R6.Leaf
open NLogN

/-- `LineNeed6` reduces to the published top-level assembler `lineBody6_top` together with
`pipeDisc6_all` and the two table-level leaves `ail6s_of_fine` / `axisU6_of_fine`.

By definition,
`LineNeed6 P` asks that every table satisfying `SwapNeedτ`, `RowUCP`, and `FineU6`
also satisfy `LineBody6 P`. Given those table hypotheses, `ail6s_of_fine` supplies
`AIL6s`, `axisU6_of_fine` supplies `AxisU6`, and `pipeDisc6_all` supplies `PipeDisc6`;
`lineBody6_top` turns the three into `LineBody6`. -/
theorem solution (P : Prm) (hP : P.Ok) : LineNeed6 P := by
  intro tab hSw hRow hFU
  exact lineBody6_top P hP tab
    (ail6s_of_fine P hP tab hSw hRow hFU)
    (axisU6_of_fine P hP tab hSw hRow hFU)
    (pipeDisc6_all P hP)
