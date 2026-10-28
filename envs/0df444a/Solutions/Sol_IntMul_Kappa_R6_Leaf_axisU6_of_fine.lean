-- Prove2me | solution 1 for IntMul.Kappa.R6.Leaf.axisU6_of_fine
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:33:54.090411+00:00
-- url     : https://prove2.me/submissions/ef2bb882-9030-41bb-8753-6f9658417514

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_Ax_axisU6_of
import Theorems.Thm_J6Seg_Src_slabNeed6
import Theorems.Thm_J6Seg_PJ_preNeed6_holds
import Theorems.Thm_J6Seg_ChB_axBudget6_ap6

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.Ax J6Seg.PJ J6Seg.ChB J6Seg.Src J6Seg.Val J6Seg.AxCh
open IntMul.Kappa.R6
open NLogN

/-- `AxisU6` under the `LineNeed6` table hypotheses is `axisU6_of` at the concrete
plan `ap6`, with `ValCond6` / `ChunkPlan6` by `decide`, `PreNeed6` from
`preNeed6_holds`, `AxBudget6` from `axBudget6_ap6`, and `SlabNeed6` from
`slabNeed6`. -/
theorem solution (P : Prm) (hP : P.Ok) (tab : Fin 1 → IStmt HS 1)
    (hSw : IL.SwapNeedτ tab P.τ) (hRow : IL2.RowUCP 576 P.τ tab) (hFU : FineU6 tab) :
    AxisU6 P tab := by
  have hVC : ValCond6 ap6 := by unfold ValCond6 ap6; decide
  have hCP : ChunkPlan6 ap6 := by unfold ChunkPlan6 ap6; decide
  exact axisU6_of P hP ap6 hVC hCP (preNeed6_holds P hP ap6.pl)
    (axBudget6_ap6 P hP) (slabNeed6 P hP) tab hSw hRow hFU
