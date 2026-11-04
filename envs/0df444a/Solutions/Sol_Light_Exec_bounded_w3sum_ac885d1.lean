-- Prove2me | solution 1 for Light.Exec.bounded_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:25.049319+00:00
-- url     : https://prove2.me/submissions/676263ce-f00c-484b-b18b-1ded672f7736

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Theorems.Thm_Light_Expr_abs_val_le
import Theorems.Thm_Light_bounded_callFrame
section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
private theorem abs_update_le {f : ℕ → ℤ} {B v : ℤ} (hf : ∀ y, |f y| ≤ B) (hv : |v| ≤ B)
    (x y : ℕ) : |Function.update f x v y| ≤ B := by
  rw [Function.update_apply]
  split_ifs
  exacts [hv, hf y]
end Light
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Exec
theorem _root_.solution {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by
  induction h with
  | skip => exact hσ
  | set hs => exact ⟨abs_update_le hσ.1 (Expr.abs_val_le hσ _ hs) _, hσ.2⟩
  | store _ he _ => exact ⟨hσ.1, abs_update_le hσ.2 (Expr.abs_val_le hσ _ he) _⟩
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | iteTrue _ _ _ ih => exact ih hσ
  | iteFalse _ _ _ ih => exact ih hσ
  | whileFalse _ _ => exact hσ
  | whileTrue _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | call ha _ _ _ ih =>
    have hbody := ih (bounded_callFrame hσ _ ha)
    exact ⟨abs_update_le hσ.1 (hbody.1 0) _, hbody.2⟩
end Exec
end Light
