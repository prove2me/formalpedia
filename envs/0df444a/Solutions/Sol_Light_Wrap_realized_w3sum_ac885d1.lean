-- Prove2me | solution 1 for Light.Wrap.realized_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:43.417242+00:00
-- url     : https://prove2.me/submissions/c69be4b5-271f-4277-8a3c-843357aeecb0

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_Wrap_topSolves
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_solves_of_programSolves
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
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
open Light.Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}
namespace Light.Wrap
theorem _root_.solution (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) : Realized Q T := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  intro κ
  obtain ⟨s, k, htop⟩ := w.topSolves hpoly hsol hT κ
  refine ⟨_, _, (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) * (w.extra κ + 1),
    by positivity,
    (solves_of_programSolves htop (r := 1) fun x => by simp).mono le_rfl (fun _ hx => hx)
      fun x _ => ?_⟩
  -- `K (T + E) + K ≤ K (E + 1) T + K (E + 1)` for `K, E, T ≥ 0`
  have hT0 : (0 : ℝ) ≤ max (T x.n x.U) 0 := le_max_right _ _
  have hK : (0 : ℝ) ≤ (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) := by positivity
  have hE : (0 : ℝ) ≤ (w.extra κ : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hK hE) hT0]
end Light.Wrap
