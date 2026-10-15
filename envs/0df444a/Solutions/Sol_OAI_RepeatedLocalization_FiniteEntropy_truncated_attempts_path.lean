-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:33:49.742997+00:00
-- url     : https://prove2.me/submissions/aa128927-93cb-476f-9320-8ca70cf68271

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/TruncatedBounds.lean:L77-L132
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_attemptLetter_some_iff
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_run_mem_event
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_descendant_of_mem

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma state_nil {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    state P Q [] = ⟨Q,cellSet Q,false⟩ := rfl

lemma state_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    state P Q (h++[a]) = update P (state P Q h) a := by
  simp only [state,List.foldl_append,List.foldl_cons,List.foldl_nil]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Rewards ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma accumulate_append {n : ℕ} (P : Measure (Coordinate n)) (r : State n → Letter n → ℝ)
    (s : State n) (h k : Log n) :
    accumulate P r s (h++k) = accumulate P r s h + accumulate P r (h.foldl (update P) s) k := by
  induction h generalizing s with
  | nil => simp [accumulate]
  | cons a h ih => simp only [List.cons_append,accumulate,List.foldl_cons,ih]; ring

lemma rewardLog_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (h : Log n) (a : Letter n) :
    rewardLog P Q r (h++[a]) = rewardLog P Q r h + r (state P Q h) a := by
  simp only [rewardLog,accumulate_append,accumulate,add_zero,state]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.TruncatedBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma rewardLog_run_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (hr : ∀ s a,s.stopped = true → r s a = 0)
    (N : ℕ) (z : Coordinate n) :
    rewardLog P Q r (run P Q (N+1) z) = rewardLog P Q r (run P Q N z) + rewardStep P Q r N z := by
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp only [run,hs,ite_true,rewardStep,hr _ _ hs,add_zero]
  · simp only [run,hs,Bool.false_eq_true,ite_false,rewardLog_append,rewardStep]

lemma continuingTotal_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    continuingTotal P Q (N+1) z = continuingTotal P Q N z + rewardStep P Q (continuingReward P) N z :=
  rewardLog_run_succ P Q _ (fun s a hs => by simp [continuingReward,hs]) N z

lemma truncatedAttempts_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    (truncatedAttempts P Q (N+1) z : ℝ) = truncatedAttempts P Q N z + activeIndicator P Q N z := by
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp [truncatedAttempts,activeIndicator,run,hs]
  · simp [truncatedAttempts,activeIndicator,run,hs,List.length_append]

lemma truncated_attempts_path {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    (truncatedAttempts P Q N z : ℝ) ≤ truncatedDepth P Q N z + continuingTotal P Q N z +
      (if (state P Q (run P Q N z)).stopped then (1:ℝ) else 0) := by
  induction N with
  | zero => simp [truncatedAttempts,truncatedDepth,continuingTotal,rewardLog,run,state_nil,accumulate]
  | succ N ih =>
    have hzE := run_mem_event P Q N hz
    have hdesc := state_descendant_of_mem P Q (run P Q N z) hzE
    by_cases hs : (state P Q (run P Q N z)).stopped = true
    · simpa only [truncatedAttempts,truncatedDepth,continuingTotal,run,hs,ite_true] using ih
    let s := state P Q (run P Q N z)
    let a := attemptLetter (ProbabilityTheory.cond P s.event) s.cell z
    have hs' : s.stopped = false := Bool.eq_false_iff.mpr hs
    have erun : run P Q (N+1) z = run P Q N z ++ [a] := by simp only [run,hs,Bool.false_eq_true,ite_false]; rfl
    have eqA := truncatedAttempts_succ P Q N z
    have eqC := continuingTotal_succ P Q N z
    have hih : (truncatedAttempts P Q N z : ℝ) ≤ truncatedDepth P Q N z + continuingTotal P Q N z := by
      simpa only [hs,Bool.false_eq_true,ite_false,add_zero] using ih
    rw [eqA,eqC]
    simp only [activeIndicator,hs,Bool.false_eq_true,ite_false,rewardStep]
    change _ ≤ truncatedDepth P Q (N+1) z + (continuingTotal P Q N z + continuingReward P s a) +
      (if (state P Q (run P Q (N+1) z)).stopped then 1 else 0)
    rw [erun,state_append]
    change _ ≤ truncatedDepth P Q (N+1) z + (continuingTotal P Q N z + continuingReward P s a) +
      (if (update P s a).stopped then 1 else 0)
    cases ha : a with
    | none =>
      have eqD : truncatedDepth P Q (N+1) z = truncatedDepth P Q N z := by
        simp only [truncatedDepth,erun,state_append,ha,update,hs,Bool.false_eq_true,ite_false,Option.getD_none]
      rw [eqD]
      have hstop : (update P s none).stopped = decide ((1/2:ℝ) ≤ complementMass P s) := by
        simp [update,hs',branch,complementMass]
      rw [hstop]
      by_cases hq : complementMass P s < 1/2
      · have hq' : ¬(1/2:ℝ) ≤ complementMass P s := not_le.mpr hq
        simp only [continuingReward,hs',Bool.false_eq_true,ite_false,true_and,ite_eq_left hq,
          decide_eq_true_eq,ite_eq_right hq',add_zero]
        linarith
      · have hq' : (1/2:ℝ) ≤ complementMass P s := le_of_not_gt hq
        simp only [continuingReward,hs',Bool.false_eq_true,ite_false,true_and,ite_eq_right hq,
          decide_eq_true_eq,ite_eq_left hq',add_zero]
        linarith
    | some R =>
      have hR : FirstHeavy (ProbabilityTheory.cond P s.event) s.cell R :=
        ((attemptLetter_some_iff hn _ _ R z).mp ha).1
      have eqD : truncatedDepth P Q (N+1) z = truncatedDepth P Q N z + (R.1-s.cell.1) := by
        simp only [truncatedDepth,erun,state_append,ha,update,hs,Bool.false_eq_true,ite_false,Option.getD_some]
        have hbase : Q.1 ≤ s.cell.1 := hdesc.1
        have hnext : s.cell.1 ≤ R.1 := hR.1.1.1
        change R.1-Q.1 = s.cell.1-Q.1+(R.1-s.cell.1)
        omega
      rw [eqD,Nat.cast_add]
      simp only [update,hs',Bool.false_eq_true,ite_false,reduceCtorEq,continuingReward,false_and,add_zero]
      have hd : (1:ℝ) ≤ (R.1-s.cell.1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hR.1.2.1
      linarith

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    (truncatedAttempts P Q N z : ℝ) ≤ truncatedDepth P Q N z + continuingTotal P Q N z +
      (if (state P Q (run P Q N z)).stopped then (1:ℝ) else 0) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path hn P Q N hz
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path
    | (apply OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path <;> assumption)
