-- Prove2me | solution 2 for J6Seg.ChB.axBudget6_ap6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:39:03.675425+00:00
-- url     : https://prove2.me/submissions/c4edbaa7-98dd-4879-89a4-13582bdc3ae4
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

/-- `AxBudget6` at `ap6` assembles `axBudget6_of` from the three budget leaves
`sideCost6_all`, `jBudget6_all`, and `chunkBudget6_all`, with the plan
side-conditions `ValCond6`, `ChunkPlan6`, and `ChunkPlanB` discharged by `decide`. -/
theorem solution (P : Prm) (hP : P.Ok) : AxBudget6 P ap6 := by
  have hVC : ValCond6 ap6 := by unfold ValCond6 ap6; decide
  have hCP : ChunkPlan6 ap6 := by unfold ChunkPlan6 ap6; decide
  have hCB : ChunkPlanB ap6 := by unfold ChunkPlanB ap6; decide
  exact axBudget6_of P hP ap6
    (sideCost6_all P hP ap6 hVC hCP)
    (jBudget6_all P hP ap6 hVC hCP)
    (chunkBudget6_all P hP ap6 hCP hCB)
