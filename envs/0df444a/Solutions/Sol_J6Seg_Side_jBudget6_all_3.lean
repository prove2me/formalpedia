-- Prove2me | solution 3 for J6Seg.Side.jBudget6_all
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:50:30.479915+00:00
-- url     : https://prove2.me/submissions/1ae249ff-4a1b-49ea-b637-f0e4ce500c5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_Side_axJ_ev
import Theorems.Thm_J6Seg_Side_jbudget_at

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open IntMul.Kappa.R6 J6Seg J6Seg.Side J6Seg.Val J6Seg.AxCh

private theorem KJc_nonneg (P : Prm) (ap : AxPlan6) : 0 ≤ KJc P ap := by
  unfold KJc; positivity

/-- `JBudget6` from eventual `AxJ` (`axJ_ev`) and `jbudget_at`. -/
theorem solution (P : Prm) (hP : P.Ok) (ap : AxPlan6)
    (hc : ValCond6 ap) (_hc' : ChunkPlan6 ap) : JBudget6 P ap := by
  obtain ⟨n₁, hN⟩ := axJ_ev P hP
  exact ⟨KJc P ap, 2, n₁, KJc_nonneg P ap, fun n hn src hsrc D hD k hk =>
    jbudget_at ap (hN n hn src hsrc D hD k hk) hc hD⟩

end
