-- Prove2me | solution 1 for J6Seg.ChB.axBudget6_ap6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:38:03.696432+00:00
-- url     : https://prove2.me/submissions/9248e6a7-dec4-436e-bd6c-f60cb60f8b38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_ChB_axBudget6_of
import Theorems.Thm_J6Seg_Side_sideCost6_all
import Theorems.Thm_J6Seg_Side_jBudget6_all
import Theorems.Thm_J6Seg_ChB_chunkBudget6_all

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.ChB J6Seg.Side J6Seg.Val J6Seg.AxCh
open IntMul.Kappa.R6

/-- `AxBudget6` at the concrete plan `ap6`: decide the plan predicates, then
`axBudget6_of` with the three published halves. -/
theorem solution (P : Prm) (hP : P.Ok) : AxBudget6 P ap6 := by
  have hVC : ValCond6 ap6 := by unfold ValCond6 ap6; decide
  have hCP : ChunkPlan6 ap6 := by unfold ChunkPlan6 ap6; decide
  have hCB : ChunkPlanB ap6 := by unfold ChunkPlanB ap6; decide
  exact axBudget6_of P hP ap6
    (sideCost6_all P hP ap6 hVC hCP)
    (jBudget6_all P hP ap6 hVC hCP)
    (chunkBudget6_all P hP ap6 hCP hCB)
