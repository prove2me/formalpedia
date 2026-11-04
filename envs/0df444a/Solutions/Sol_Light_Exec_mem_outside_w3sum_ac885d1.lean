-- Prove2me | solution 1 for Light.Exec.mem_outside_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:26.299775+00:00
-- url     : https://prove2.me/submissions/552a0a05-61cb-4436-a911-bdb0f251b7c5

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits

set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Exec
theorem _root_.solution {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (a : ℕ)
    (ha : lim.space ≤ a) : σ'.mem a = σ.mem a := by
  induction h with
  | skip => rfl
  | set _ => rfl
  | store _ _ haddr =>
    obtain ⟨h0, hlt⟩ := haddr
    exact Function.update_of_ne (by omega) _ _
  | seq _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | call _ _ _ _ ih => exact ih
end Exec
end Light
