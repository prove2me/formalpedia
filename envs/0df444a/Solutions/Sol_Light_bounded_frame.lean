-- Prove2me | solution 1 for Light.bounded_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:07.363391+00:00
-- url     : https://prove2.me/submissions/7f7ed820-6b76-4673-bf04-fd9ebeab2e92

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le


set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ :=
  ⟨ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩
end Light
