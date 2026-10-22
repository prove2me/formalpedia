-- Prove2me | solution 1 for J6Seg.Side.sideCost6_all
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:36:42.57306+00:00
-- url     : https://prove2.me/submissions/d5ea3ff0-434e-4b44-9bcb-5505775cc5a6

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_Side_axNum_ev
import Theorems.Thm_J6Seg_Side_side_at

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.Side J6Seg.Val J6Seg.AxCh
open IntMul.Kappa.R6

private theorem Kc_nonneg (P : Prm) (ap : AxPlan6) : 0 ≤ Kc P ap := by
  unfold Kc
  positivity

/-- `SideCost6` from `axNum_ev` and `side_at`; plan hypotheses unused. -/
theorem solution (P : Prm) (hP : P.Ok) (ap : AxPlan6)
    (_hc : ValCond6 ap) (_hc' : ChunkPlan6 ap) : SideCost6 P ap := by
  obtain ⟨n₁, hN⟩ := axNum_ev P hP
  exact ⟨Kc P ap, 2, n₁, Kc_nonneg P ap, fun n hn src hsrc D hD k hk =>
    side_at P ap (hN n hn src hsrc D hD k hk) hD⟩
