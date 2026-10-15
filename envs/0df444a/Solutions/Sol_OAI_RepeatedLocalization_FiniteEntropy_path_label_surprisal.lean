-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:24:40.652688+00:00
-- url     : https://prove2.me/submissions/ad397e0d-5a78-42dc-b153-110e82c380be

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Rewards.lean:L126-L174
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_descendant_of_mem

-- ---- from OAI.Probability.Localization.Cells ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellSet_eq_pi {n : ℕ} (Q : Cell n) :
    cellSet Q = Set.pi univ (fun i => Ico (cellLower Q i) (cellLower Q i + cellWidth n Q.1)) := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ico]
  congr! 3
  simp only [cellLower, cellWidth]
  ring

lemma measurableSet_cellSet {n : ℕ} (Q : Cell n) : MeasurableSet (cellSet Q) := by
  rw [cellSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.FirstHeavy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma measurableSet_residual {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet (residual P Q) :=
  (measurableSet_cellSet Q).diff (MeasurableSet.iUnion (fun R => measurableSet_cellSet R.val))

lemma measurableSet_branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (a : Letter n) :
    MeasurableSet (branch P Q a) := by
  classical
  cases a with
  | none => exact measurableSet_residual P Q
  | some R => by_cases h : FirstHeavy P Q R <;> simp [branch,h,measurableSet_cellSet]

end FiniteEntropy

end RepeatedLocalization

end OAI

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

lemma state_event_measurable {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    MeasurableSet (state P Q h).event := by
  induction h using List.reverseRecOn with
  | nil => exact measurableSet_cellSet Q
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · exact ih.inter (measurableSet_branch _ _ _)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Rewards ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

lemma threshold_pos (n h : ℕ) : 0 < threshold n h := Real.rpow_pos_of_pos (by norm_num) _

lemma log_threshold (n h : ℕ) : Real.log (threshold n h) = -(n:ℝ)*(h:ℝ)/2*Real.log 2 := by
  exact Real.log_rpow (by norm_num) _

lemma positive_event_descendant {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n)
    (hp : P (state P Q h).event ≠ 0) : Descendant Q (state P Q h).cell := by
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hp
  exact state_descendant_of_mem P Q h hz

lemma state_event_append_subset {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    (state P Q (h++[a])).event ⊆ (state P Q h).event := by
  rw [state_append]
  unfold update
  split
  · exact Subset.rfl
  · exact Set.inter_subset_left

lemma cond_event_mul {α : Type*} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P]
    {E B : Set α} (hE : MeasurableSet E) (hp : P E ≠ 0) :
    (P (E∩B)).toReal = (P E).toReal * ((ProbabilityTheory.cond P E) B).toReal := by
  rw [ProbabilityTheory.cond_apply hE,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hp' : (P E).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp,measure_ne_top _ _⟩
  exact (mul_inv_cancel_left₀ hp' _).symm

lemma path_label_surprisal {n : ℕ} (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hroot : P (cellSet Q) = 1) (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    -Real.log (P (state P Q h).event).toReal ≤
      ((n:ℝ)*Real.log 2/2)*((state P Q h).cell.1-Q.1 : ℕ) + rewardLog P Q (complementReward P) h := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp only [state_nil,hroot,ENNReal.toReal_one,Real.log_one,neg_zero,Nat.sub_self,
      Nat.cast_zero,mul_zero,rewardLog,accumulate,add_zero,le_refl]
  | append_singleton h a ih =>
    have hp0 : P (state P Q h).event ≠ 0 := by
      intro he
      exact hp (measure_mono_null (state_event_append_subset P Q h a) he)
    have hih := ih hp0
    have ppos : 0 < (P (state P Q h).event).toReal := ENNReal.toReal_pos hp0 (measure_ne_top _ _)
    have hdesc := positive_event_descendant P Q h hp0
    rw [state_append,rewardLog_append]
    by_cases hs : (state P Q h).stopped = true
    · simpa only [update,hs,ite_true,complementReward,add_zero] using hih
    · cases a with
      | none =>
        have he : (P (update P (state P Q h) none).event).toReal =
            (P (state P Q h).event).toReal * complementMass P (state P Q h) := by
          simp only [update,hs,branch,complementMass]
          exact cond_event_mul P (state_event_measurable P Q h) hp0
        have hepos : 0 < (P (update P (state P Q h) none).event).toReal :=
          ENNReal.toReal_pos (by simpa only [state_append] using hp) (measure_ne_top _ _)
        have hqpos : 0 < complementMass P (state P Q h) := by rw [he] at hepos; nlinarith [complementMass_nonneg P (state P Q h)]
        rw [he,Real.log_mul ppos.ne' hqpos.ne']
        simp only [update,hs,Bool.false_eq_true,ite_false,Option.getD_none,complementReward,ite_true]
        linarith
      | some R =>
        have hR : FirstHeavy (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell R := by
          by_contra hR
          simp [state_append,update,hs,branch,hR] at hp
        have he : (P (update P (state P Q h) (some R)).event).toReal =
            (P (state P Q h).event).toReal * ((ProbabilityTheory.cond P (state P Q h).event) (cellSet R)).toReal := by
          simp only [update,hs,branch,ite_eq_left hR]
          exact cond_event_mul P (state_event_measurable P Q h) hp0
        have hmpos := (threshold_pos n (R.1-(state P Q h).cell.1)).trans hR.1.2.2
        have hl := Real.log_le_log (threshold_pos n (R.1-(state P Q h).cell.1)) hR.1.2.2.le
        rw [log_threshold] at hl
        have hdepth : R.1-Q.1 = ((state P Q h).cell.1-Q.1)+(R.1-(state P Q h).cell.1) := by
          have := hdesc.1
          have := hR.1.1.1
          omega
        rw [he,Real.log_mul ppos.ne' hmpos.ne']
        simp only [update,hs,Bool.false_eq_true,ite_false,Option.getD_some,complementReward,reduceCtorEq,add_zero]
        rw [hdepth,Nat.cast_add]
        nlinarith

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hroot : P (cellSet Q) = 1) (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    -Real.log (P (state P Q h).event).toReal ≤
      ((n:ℝ)*Real.log 2/2)*((state P Q h).cell.1-Q.1 : ℕ) + rewardLog P Q (complementReward P) h := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal P Q hroot h hp
    | exact OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal
    | (apply OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal <;> assumption)
