-- Prove2me | solution 1 for Light.Wrap.topSolves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:13.767538+00:00
-- url     : https://prove2.me/submissions/82863368-66c9-4c3a-aa31-b90aebee35e5

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_ofEnd_input_le
import Theorems.Thm_Light_Wrap_room
import Theorems.Thm_Light_Wrap_body_ends
import Theorems.Thm_Light_Wrap_body_ends_zero
import Theorems.Thm_Light_Wrap_ends_of_body
import Theorems.Thm_Light_Wrap_small
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
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
open Light.Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}
namespace Light.Wrap
theorem _root_.solution (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (hsol : Solves task P p Tn need)
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u) (κ : ℕ) :
    ∃ s k : ℕ, ProgramSolves (ofEnd Q) (P ++ [topBody κ p w.args dec]) P.length dec s k
      (fun x => x.U = x.n ^ κ) fun x => max (T x.n x.U) 0 + w.extra κ := by
  obtain ⟨s, k, hsmall⟩ := w.small hpoly κ
  refine ⟨s, k, fun x hU => ?_⟩
  have hinput : ∀ a ∈ (ofEnd Q).input x, |a| ≤ (w.limits need x).word := fun a ha =>
    (ofEnd_input_le x a ha).trans (by simp only [limits]; omega)
  rcases Nat.eq_zero_or_pos x.n with hn | hn
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends_zero P p κ x hn (w.room need x))
    have hc' : (c : ℝ) ≤ w.extra κ := by exact_mod_cast hc.trans (by unfold extra bodySteps; omega)
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_right (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends hsol κ x hn hU (w.room need x))
    have hc' : (c : ℝ) ≤ (Tn x.n x.U : ℝ) + w.extra κ := by
      exact_mod_cast hc.trans (by unfold extra; omega)
    have hTn := hT x.n x.U x.U hn (hU ▸ Nat.one_le_pow _ _ hn) le_rfl
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_left (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩
end Light.Wrap
