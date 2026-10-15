-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:38:28.560301+00:00
-- url     : https://prove2.me/submissions/4699cb14-7576-46f1-974d-1b7f92aa0620

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/EntropyBudget.lean:L105-L123
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral. The node keeps its source
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
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_attempts_path
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

lemma truncated_attempts_integral {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(truncatedAttempts P Q N z:ℝ) ∂P) ≤ 2*(1+∫ z,(truncatedDepth P Q N z:ℝ) ∂P) := by
  have hroot := ae_mem_cell_of_ac hac
  have hC := (truncated_reward_bounds hn P Q hroot N).2
  have hD := truncated_depth_integrable hn P Q hac hK N
  have hp : ∀ᵐ z ∂P,(truncatedAttempts P Q N z:ℝ) ≤
      (truncatedDepth P Q N z:ℝ) + continuingTotal P Q N z + 1 := by
    filter_upwards [hroot] with z hz
    have hb := truncated_attempts_path hn P Q N hz
    have hs : (if (state P Q (run P Q N z)).stopped then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
    linarith
  have hi := integral_mono_ae (integrable_truncatedAttempts hn P Q N)
    ((hD.add hC.1).add (integrable_const 1)) hp
  have had := integral_add (hD.add hC.1) (integrable_const (1:ℝ))
  simp only [Pi.add_apply] at hi had
  rw [had,integral_add hD hC.1] at hi
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hi
  linarith [hC.2.2]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(truncatedAttempts P Q N z:ℝ) ∂P) ≤ 2*(1+∫ z,(truncatedDepth P Q N z:ℝ) ∂P) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral hn P Q hac hK N
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral
    | (apply OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral <;> assumption)
