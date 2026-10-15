-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:32:10.500334+00:00
-- url     : https://prove2.me/submissions/b9475e59-661b-4a6e-aac1-78a5a4c44568

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/TruncatedBounds.lean:L49-L75
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_run
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_rewardStep_integral_bound

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma run_length_le {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    (run P Q N z).length ≤ N := by
  induction N with
  | zero => simp [run]
  | succ N ih =>
    simp only [run]
    split
    · exact ih.trans (Nat.le_succ N)
    · simpa only [List.length_append,List.length_singleton] using Nat.add_le_add_right ih 1

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

lemma complementMass_nonneg {n : ℕ} (P : Measure (Coordinate n)) (s : State n) :
    0 ≤ complementMass P s := ENNReal.toReal_nonneg

lemma complementMass_le_one {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P] (s : State n) :
    complementMass P s ≤ 1 := by
  by_cases hp : P s.event = 0
  · simp [complementMass,ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hp]
  · let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hp
    exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq ENNReal.toReal_one

lemma complementReward_nonneg {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (s : State n) (a : Letter n) : 0 ≤ complementReward P s a := by
  unfold complementReward
  split
  · exact le_rfl
  · split
    · exact neg_nonneg.mpr (Real.log_nonpos (complementMass_nonneg P s) (complementMass_le_one P s))
    · exact le_rfl

lemma continuingReward_nonneg {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) :
    0 ≤ continuingReward P s a := by unfold continuingReward; split_ifs <;> norm_num

lemma neg_log_mul_le {q : ℝ} (hq : 0 ≤ q) : q * (-Real.log q) ≤ 1/Real.exp 1 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp only [Real.log_zero,neg_zero,mul_zero]; positivity
  · have hl := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (-1)) hq)
    rw [Real.log_div (Real.exp_ne_zero _) hq.ne',Real.log_exp] at hl
    have hh := mul_le_mul_of_nonneg_left hl hq.le
    have he : q * (Real.exp (-1) / q - 1) = Real.exp (-1)-q := by field_simp
    rw [he,Real.exp_neg,← one_div] at hh
    nlinarith

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.RewardBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma integrable_activeIndicator {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (Q : Cell n) (hn : 0 < n) (N : ℕ) : Integrable (activeIndicator P Q N) P := by
  have he : activeIndicator P Q N = {z | (state P Q (run P Q N z)).stopped = false}.indicator (fun _ => (1:ℝ)) := by
    funext z
    simp only [activeIndicator,Set.indicator_apply,Set.mem_ofPred_eq]
    by_cases hs : (state P Q (run P Q N z)).stopped = true
    · simp [hs]
    · simp [Bool.eq_false_iff.mpr hs]
  rw [he]
  exact (integrable_const _).indicator
    (((measurable_of_countable (fun h : Log n => (state P Q h).stopped)).comp
      (measurable_run hn P Q N)) (measurableSet_singleton false))

lemma complementReward_some {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (R : Cell n) :
    complementReward P s (some R) = 0 := by simp [complementReward]

lemma continuingReward_some {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (R : Cell n) :
    continuingReward P s (some R) = 0 := by simp [continuingReward]

lemma complementStep_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (rewardStep P Q (complementReward P) N) P ∧
      (∫ z,rewardStep P Q (complementReward P) N z ∂P) ≤
        (1/Real.exp 1)*(∫ z,activeIndicator P Q N z ∂P) := by
  apply rewardStep_integral_bound hn P Q hroot _ (complementReward_nonneg P) (complementReward_some P)
  intro s
  by_cases hs : s.stopped = true
  · simp [complementReward,hs]
  · simpa [complementReward,hs] using neg_log_mul_le (complementMass_nonneg P s)

lemma continuingStep_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (rewardStep P Q (continuingReward P) N) P ∧
      (∫ z,rewardStep P Q (continuingReward P) N z ∂P) ≤
        (1/2:ℝ)*(∫ z,activeIndicator P Q N z ∂P) := by
  apply rewardStep_integral_bound hn P Q hroot _ (continuingReward_nonneg P) (continuingReward_some P)
  intro s
  by_cases hs : s.stopped = true
  · simp [continuingReward,hs]
  · by_cases hq : complementMass P s < 1/2
    · simpa only [continuingReward,hs,Bool.false_eq_true,ite_false,true_and,ite_eq_left hq,mul_one] using hq.le
    · simp only [continuingReward,hs,Bool.false_eq_true,ite_false,true_and,ite_eq_right hq,mul_zero,mul_one]
      norm_num

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.TruncatedBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma complementTotal_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    complementTotal P Q (N+1) z = complementTotal P Q N z + rewardStep P Q (complementReward P) N z :=
  rewardLog_run_succ P Q _ (fun s a hs => by simp [complementReward,hs]) N z

lemma continuingTotal_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    continuingTotal P Q (N+1) z = continuingTotal P Q N z + rewardStep P Q (continuingReward P) N z :=
  rewardLog_run_succ P Q _ (fun s a hs => by simp [continuingReward,hs]) N z

lemma truncatedAttempts_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    (truncatedAttempts P Q (N+1) z : ℝ) = truncatedAttempts P Q N z + activeIndicator P Q N z := by
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp [truncatedAttempts,activeIndicator,run,hs]
  · simp [truncatedAttempts,activeIndicator,run,hs,List.length_append]

lemma measurable_truncatedAttempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    Measurable (fun z => (truncatedAttempts P Q N z : ℝ)) :=
  (measurable_of_countable (fun h : Log n => (h.length:ℝ))).comp (measurable_run hn P Q N)

lemma integrable_truncatedAttempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (N : ℕ) : Integrable (fun z => (truncatedAttempts P Q N z : ℝ)) P := by
  apply Integrable.mono' (integrable_const (N:ℝ)) (measurable_truncatedAttempts hn P Q N).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast run_length_le P Q N z)

lemma truncated_reward_bounds {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (complementTotal P Q N) P ∧ Integrable (continuingTotal P Q N) P ∧
    (∫ z,complementTotal P Q N z ∂P) ≤ (1/Real.exp 1)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) ∧
    (∫ z,continuingTotal P Q N z ∂P) ≤ (1/2:ℝ)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) := by
  induction N with
  | zero =>
    have hJ : complementTotal P Q 0 = fun _ => 0 := rfl
    have hC : continuingTotal P Q 0 = fun _ => 0 := rfl
    simp [hJ,hC,truncatedAttempts,run]
  | succ N ih =>
    have hJ := complementStep_bound hn P Q hroot N
    have hC := continuingStep_bound hn P Q hroot N
    have eqJ : complementTotal P Q (N+1) = complementTotal P Q N + rewardStep P Q (complementReward P) N :=
      funext (complementTotal_succ P Q N)
    have eqC : continuingTotal P Q (N+1) = continuingTotal P Q N + rewardStep P Q (continuingReward P) N :=
      funext (continuingTotal_succ P Q N)
    rw [eqJ,eqC]
    refine ⟨ih.1.add hJ.1,ih.2.1.add hC.1,?_,?_⟩
    · simp only [Pi.add_apply]
      simp_rw [truncatedAttempts_succ]
      rw [integral_add ih.1 hJ.1,integral_add (integrable_truncatedAttempts hn P Q N) (integrable_activeIndicator P Q hn N)]
      nlinarith [ih.2.2.1,hJ.2]
    · simp only [Pi.add_apply]
      simp_rw [truncatedAttempts_succ]
      rw [integral_add ih.2.1 hC.1,integral_add (integrable_truncatedAttempts hn P Q N) (integrable_activeIndicator P Q hn N)]
      nlinarith [ih.2.2.2,hC.2]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (complementTotal P Q N) P ∧ Integrable (continuingTotal P Q N) P ∧
    (∫ z,complementTotal P Q N z ∂P) ≤ (1/Real.exp 1)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) ∧
    (∫ z,continuingTotal P Q N z ∂P) ≤ (1/2:ℝ)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds hn P Q hroot N
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds
    | (apply OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds <;> assumption)
