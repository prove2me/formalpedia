-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:40:21.051167+00:00
-- url     : https://prove2.me/submissions/76c638f9-40cc-46bb-a6cc-c7272447ab97

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/EntropyBudget.lean:L132-L149
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget. The node keeps its source
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
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_reward_bounds

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

-- ---- from OAI.Probability.Localization.ConditionalLaws ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma uniformCell_ae_mem {n : ℕ} (Q : Cell n) : ∀ᵐ z ∂uniformCell Q,z ∈ cellSet Q :=
  ProbabilityTheory.ae_cond_mem (measurableSet_cellSet Q)

lemma ae_mem_cell_of_ac {n : ℕ} {P : Measure (Coordinate n)} {Q : Cell n}
    (hac : P ≪ uniformCell Q) : ∀ᵐ z ∂P,z ∈ cellSet Q := hac.ae_le (uniformCell_ae_mem Q)

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

lemma slope_absorption {n : ℕ} (hn : 32 ≤ n) : 2/Real.exp 1 ≤ entropySlope n/2 := by
  have hn' : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hl : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : (2:ℝ)/Real.exp 1 ≤ 2 := (div_le_self (by norm_num) (Real.one_le_exp (by norm_num)))
  unfold entropySlope
  nlinarith

lemma truncated_final_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(historyKL P Q (run P Q N z)).toReal + entropySlope n/2*(truncatedDepth P Q N z:ℝ) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by
  have hn0 : 0 < n := by omega
  have hcost := (truncated_cost_bound hn0 P Q hac hK N).2
  have hJ := (truncated_reward_bounds hn0 P Q (ae_mem_cell_of_ac hac) N).2.2.1
  have hA := truncated_attempts_integral hn0 P Q hac hK N
  have hD := truncated_depth_integrable hn0 P Q hac hK N
  have hKI := truncated_KL_integrable hn0 P Q hac hK N
  change (∫ z,(historyKL P Q (run P Q N z)).toReal + entropySlope n*(truncatedDepth P Q N z:ℝ) ∂P) ≤ _ at hcost
  rw [integral_add hKI (hD.const_mul (entropySlope n)),integral_const_mul] at hcost
  rw [integral_add hKI (hD.const_mul (entropySlope n / 2)),integral_const_mul]
  have hD0 : 0 ≤ ∫ z,(truncatedDepth P Q N z:ℝ) ∂P := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have habs := mul_le_mul_of_nonneg_right (slope_absorption hn) hD0
  have hJA := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ (1:ℝ)/Real.exp 1)
  simp only [div_eq_mul_inv,one_mul] at hJ hJA habs ⊢
  nlinarith only [hcost,hJ,habs,hJA]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(historyKL P Q (run P Q N z)).toReal + entropySlope n/2*(truncatedDepth P Q N z:ℝ) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget hn P Q hac hK N
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget
    | (apply OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget <;> assumption)
