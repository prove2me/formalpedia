-- Prove2me | solution 1 for Light.pow_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:45.947137+00:00
-- url     : https://prove2.me/submissions/52aecbae-a6d6-4328-a9ff-12b994d39479

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_setTo
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (a : ℤ) (μ : ℕ → ℤ) :
    ∀ κ : ℕ,
      ((n ^ κ : ℕ) : ℤ) ≤ lim.word →
        Ends lim P d (powStmt κ) ⟨frame [a, n, 1], μ⟩ (4 * κ) (· = ⟨frame [a, n, ((n ^ κ : ℕ) : ℤ)], μ⟩)
  | 0, _ => Ends.skip (by simp)
  | κ + 1, hw =>
    by
    have hle : ((n ^ κ : ℕ) : ℤ) ≤ ((n ^ (κ + 1) : ℕ) : ℤ) := by exact_mod_cast Nat.pow_le_pow_right hn (by omega)
    have hval : ((n ^ κ : ℕ) : ℤ) * n = ((n ^ (κ + 1) : ℕ) : ℤ) :=
      by
      push_cast
      ring
    unfold powStmt
    refine Ends.next (4 * κ) ((solution hn a μ κ (hle.trans hw)).mono le_rfl ?_)
    rintro _ rfl
    refine Ends.setTo ((n ^ (κ + 1) : ℕ) : ℤ) rfl ⟨?_, ?_⟩
    · simp only [_root_.Light.Expr.Safe, _root_.Light.Expr.val, _root_.Light.Expr.cost, _root_.Light.Op.eval,
        _root_.Light.Cond.Holds, _root_.Light.Cond.cost, _root_.Light.Cond.Safe, _root_.Function.update_apply,
        _root_.reduceIte, _root_.true_and, _root_.and_true, _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat,
        _root_.Nat.cast_zero, _root_.Nat.cast_one, ]
      change |((n ^ κ : ℕ) : ℤ) * n| ≤ lim.word
      rw [hval, abs_of_nonneg (Int.natCast_nonneg _)]
      exact hw
    · exact hval
end Light
