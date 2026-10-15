-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.almost_sure_termination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:44:54.013544+00:00
-- url     : https://prove2.me/submissions/4b2d689d-4fe3-48a6-89f5-1d12a73780a5

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Termination.lean:L111-L137
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.almost_sure_termination. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Definitions.Def_OAI_Probability_Localization_EntropyBudget
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_run
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_attempts_integral
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_cost_bound
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_final_budget

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

lemma run_length_of_active {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    (z : Coordinate n) (ha : (state P Q (run P Q N z)).stopped = false) :
    (run P Q N z).length = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hprev : (state P Q (run P Q N z)).stopped = false := by
      cases he : (state P Q (run P Q N z)).stopped
      · rfl
      · simp only [run,he,ite_true] at ha
        exact ha
    simp only [run,hprev,Bool.false_eq_true,ite_false,List.length_append,List.length_singleton]
    rw [ih hprev]

lemma measurableSet_stopped {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    MeasurableSet {z | (state P Q (run P Q N z)).stopped = true} :=
  ((measurable_of_countable (fun h : Log n => (state P Q h).stopped)).comp
    (measurable_run hn P Q N)) (measurableSet_singleton true)

lemma measurableSet_terminates {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet {z | Terminates P Q z} := by
  have he : {z | Terminates P Q z} = ⋃ N : ℕ,{z | (state P Q (run P Q N z)).stopped = true} := by
    ext z; simp only [Terminates,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion (measurableSet_stopped hn P Q)

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

lemma measurable_truncatedAttempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    Measurable (fun z => (truncatedAttempts P Q N z : ℝ)) :=
  (measurable_of_countable (fun h : Log n => (h.length:ℝ))).comp (measurable_run hn P Q N)

lemma integrable_truncatedAttempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (N : ℕ) : Integrable (fun z => (truncatedAttempts P Q N z : ℝ)) P := by
  apply Integrable.mono' (integrable_const (N:ℝ)) (measurable_truncatedAttempts hn P Q N).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast run_length_le P Q N z)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.EntropyBudget ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma entropySlope_pos {n : ℕ} (hn : 0 < n) : 0 < entropySlope n := by
  unfold entropySlope
  exact div_pos (mul_pos (Nat.cast_pos.mpr hn) (Real.log_pos (by norm_num))) (by norm_num)

lemma truncated_depth_integrable {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => (truncatedDepth P Q N z : ℝ)) P := by
  have hc := (truncated_cost_bound hn P Q hac hK N).1
  have hm : Measurable (fun z => (truncatedDepth P Q N z : ℝ)) :=
    (measurable_of_countable (fun h : Log n => (((state P Q h).cell.1-Q.1:ℕ):ℝ))).comp (measurable_run hn P Q N)
  apply Integrable.mono' (hc.div_const (entropySlope n)) hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),le_div_iff₀ (entropySlope_pos hn)]
  change _ ≤ (historyKL P Q (run P Q N z)).toReal + entropySlope n * (truncatedDepth P Q N z:ℝ)
  nlinarith [ENNReal.toReal_nonneg (a := historyKL P Q (run P Q N z))]

lemma truncated_KL_integrable {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => (historyKL P Q (run P Q N z)).toReal) P := by
  have hc := (truncated_cost_bound hn P Q hac hK N).1
  have hd := truncated_depth_integrable hn P Q hac hK N
  have he : (fun z => (historyKL P Q (run P Q N z)).toReal) =
      (fun z => historyCost P Q (run P Q N z)) - (fun z => entropySlope n*(truncatedDepth P Q N z:ℝ)) := by
    funext z
    simp [historyCost,truncatedDepth]
  rw [he]
  exact hc.sub (hd.const_mul _)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Termination ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

open Filter
open scoped Topology

lemma truncated_uniform_attempts {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(truncatedAttempts P Q N z:ℝ) ∂P) ≤
      2*(1+((InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1)/(entropySlope n/2)) := by
  have hn0 : 0 < n := by omega
  have hB := truncated_final_budget hn P Q hac hK N
  rw [integral_add (truncated_KL_integrable hn0 P Q hac hK N)
    ((truncated_depth_integrable hn0 P Q hac hK N).const_mul _),integral_const_mul] at hB
  have hk0 : 0 ≤ ∫ z,(historyKL P Q (run P Q N z)).toReal ∂P := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have hd : (∫ z,(truncatedDepth P Q N z:ℝ) ∂P) ≤
      ((InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1)/(entropySlope n/2) := by
    rw [le_div_iff₀ (div_pos (entropySlope_pos hn0) (by norm_num))]
    nlinarith
  exact (truncated_attempts_integral hn0 P Q hac hK N).trans (by linarith)

lemma almost_sure_termination {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    ∀ᵐ z ∂P,Terminates P Q z := by
  have hn0 : 0 < n := by omega
  let E := {z | ¬Terminates P Q z}
  have hE : MeasurableSet E := (measurableSet_terminates hn0 P Q).compl
  apply ae_iff.mpr
  change P E = 0
  by_contra hp
  have hp0 : 0 < (P E).toReal := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let B := 2*(1+((InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1)/(entropySlope n/2))
  obtain ⟨N,hN⟩ := exists_nat_gt (B/(P E).toReal)
  have hconst : ∀ z ∈ E,(truncatedAttempts P Q N z:ℝ) = N := by
    intro z hz
    have ha : (state P Q (run P Q N z)).stopped = false := by
      apply Bool.eq_false_iff.mpr
      intro hs
      exact hz ⟨N,hs⟩
    exact congrArg (fun k : ℕ => (k:ℝ)) (run_length_of_active P Q N z ha)
  have hi := setIntegral_le_integral (s := E) (integrable_truncatedAttempts hn0 P Q N)
    (ae_of_all _ (fun _ => Nat.cast_nonneg _))
  rw [setIntegral_congr_fun hE hconst,integral_const] at hi
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hi
  have hb := truncated_uniform_attempts hn P Q hac hK N
  change _ ≤ B at hb
  have hN' := (div_lt_iff₀ hp0).mp hN
  nlinarith

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Filter
open scoped Topology

theorem solution {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    ∀ᵐ z ∂P,Terminates P Q z := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.almost_sure_termination hn P Q hac hK
    | exact OAI.RepeatedLocalization.FiniteEntropy.almost_sure_termination
    | (apply OAI.RepeatedLocalization.FiniteEntropy.almost_sure_termination <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.almost_sure_termination <;> assumption)
