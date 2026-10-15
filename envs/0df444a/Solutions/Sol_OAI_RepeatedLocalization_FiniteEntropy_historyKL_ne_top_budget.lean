-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:35:12.134983+00:00
-- url     : https://prove2.me/submissions/018bf652-7f2b-4c6b-94f1-6a5b93ba03fb

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/EntropyBudget.lean:L30-L49
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget. The node keeps its source
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
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_klDiv_cond_cond
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_path_label_surprisal
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_descendant_of_mem
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_event_subset_cell
import Theorems.Thm_OAI_RepeatedLocalization_cellSet_subset_initialCube
import Theorems.Thm_OAI_RepeatedLocalization_cubePrior_cellSet

-- ---- from OAI.Probability.Localization.Experiment ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma measurable_initialCube (n : ℕ) : MeasurableSet (initialCube n) := by
  apply MeasurableSet.univ_pi
  intro _
  exact measurableSet_Ico

lemma volume_initialCube (n : ℕ) :
    volume (initialCube n) = ENNReal.ofReal ((1 / Real.sqrt n) ^ n) := by
  unfold initialCube
  rw [Real.volume_pi_Ico]
  have hw : 1 / (2 * Real.sqrt n) - -1 / (2 * Real.sqrt n) = 1 / Real.sqrt n := by
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

lemma volume_initialCube_ne_top (n : ℕ) : volume (initialCube n) ≠ ∞ := by
  rw [volume_initialCube]
  exact ENNReal.ofReal_ne_top

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Cells ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellWidth_pos {n J : ℕ} (hn : 0 < n) : 0 < cellWidth n J := by
  unfold cellWidth
  positivity

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

lemma volume_cellSet {n : ℕ} (Q : Cell n) :
    volume (cellSet Q) = ENNReal.ofReal ((cellWidth n Q.1)^n) := by
  rw [cellSet_eq_pi, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by unfold cellWidth; positivity) n).symm

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

-- ---- from OAI.Probability.Localization.ConditionalLaws ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma volume_cellSet_ne_zero {n : ℕ} (hn : 0 < n) (Q : Cell n) : volume (cellSet Q) ≠ 0 := by
  rw [volume_cellSet]
  exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (cellWidth_pos hn) _)

lemma volume_cellSet_ne_top {n : ℕ} (Q : Cell n) : volume (cellSet Q) ≠ ∞ := by
  rw [volume_cellSet]
  exact ENNReal.ofReal_ne_top

lemma uniformCell_probability {n : ℕ} (hn : 0 < n) (Q : Cell n) : IsProbabilityMeasure (uniformCell Q) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (volume_cellSet_ne_zero hn Q) (volume_cellSet_ne_top Q)

lemma uniformCell_ae_mem {n : ℕ} (Q : Cell n) : ∀ᵐ z ∂uniformCell Q,z ∈ cellSet Q :=
  ProbabilityTheory.ae_cond_mem (measurableSet_cellSet Q)

lemma ae_mem_cell_of_ac {n : ℕ} {P : Measure (Coordinate n)} {Q : Cell n}
    (hac : P ≪ uniformCell Q) : ∀ᵐ z ∂P,z ∈ cellSet Q := hac.ae_le (uniformCell_ae_mem Q)

lemma uniformCell_cond {n : ℕ} {Q R : Cell n} (hQR : Descendant Q R) :
    ProbabilityTheory.cond (uniformCell Q) (cellSet R) = uniformCell R := by
  unfold uniformCell
  rw [ProbabilityTheory.cond_cond_eq_cond_inter' (measurableSet_cellSet Q)
    (measurableSet_cellSet R) (volume_cellSet_ne_top Q),Set.inter_eq_right.mpr hQR.2]

lemma uniformCell_eq_cond_prior {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    uniformCell Q = ProbabilityTheory.cond (cubePrior n) (cellSet Q) := by
  unfold cubePrior uniformCell
  rw [ProbabilityTheory.cond_cond_eq_cond_inter' (measurable_initialCube n)
    (measurableSet_cellSet Q) (volume_initialCube_ne_top n),
    Set.inter_eq_right.mpr (cellSet_subset_initialCube hn Q)]

lemma uniformCell_descendant_mass {n : ℕ} (hn : 0 < n) {Q R : Cell n} (hQR : Descendant Q R) :
    uniformCell Q (cellSet R) = ENNReal.ofReal ((1/2:ℝ)^(n*(R.1-Q.1))) := by
  rw [uniformCell_eq_cond_prior hn Q,ProbabilityTheory.cond_apply (measurableSet_cellSet Q),
    Set.inter_eq_right.mpr hQR.2,cubePrior_cellSet hn Q,cubePrior_cellSet hn R]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < (1/2:ℝ)^(n*Q.1)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : n*R.1 = n*Q.1+n*(R.1-Q.1) := by
    rw [← Nat.mul_add,Nat.add_sub_of_le hQR.1]
  rw [he,pow_add]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (1 / 2 : ℝ) ≠ 0)) _

lemma uniformCell_descendant_pos {n : ℕ} (hn : 0 < n) {Q R : Cell n} (hQR : Descendant Q R) :
    uniformCell Q (cellSet R) ≠ 0 := by
  rw [uniformCell_descendant_mass hn hQR]
  exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

lemma uniformCell_log_mass {n : ℕ} (hn : 0 < n) {Q R : Cell n} (hQR : Descendant Q R) :
    Real.log ((uniformCell Q (cellSet R)).toReal) = -(n:ℝ)*((R.1-Q.1:ℕ):ℝ)*Real.log 2 := by
  rw [uniformCell_descendant_mass hn hQR,ENNReal.toReal_ofReal (by positivity),Real.log_pow]
  simp only [one_div,Real.log_inv,Nat.cast_mul]
  ring

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

lemma positive_event_descendant {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n)
    (hp : P (state P Q h).event ≠ 0) : Descendant Q (state P Q h).cell := by
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hp
  exact state_descendant_of_mem P Q h hz

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.EntropyBudget ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma historyKL_ne_top_budget {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    historyKL P Q h ≠ ∞ ∧
    (P (state P Q h).event).toReal * historyCost P Q h ≤
      (∫ z in (state P Q h).event,llr P (uniformCell Q) z ∂P) +
        (P (state P Q h).event).toReal * rewardLog P Q (complementReward P) h := by
  let := uniformCell_probability hn Q
  have hd := positive_event_descendant P Q h hp
  have hk := klDiv_cond_cond P (uniformCell Q) hac hK (state_event_measurable P Q h)
    (measurableSet_cellSet _) (state_event_subset_cell P Q h) hp (uniformCell_descendant_pos hn hd)
  rw [uniformCell_cond hd,uniformCell_log_mass hn hd] at hk
  refine ⟨hk.1,?_⟩
  have hroot : P (cellSet Q) = 1 := (mem_ae_iff_prob_eq_one (measurableSet_cellSet Q)).mp (ae_mem_cell_of_ac hac)
  have hs := mul_le_mul_of_nonneg_left (path_label_surprisal P Q hroot h hp) (ENNReal.toReal_nonneg (a := P (state P Q h).event))
  have he := hk.2
  change (P (state P Q h).event).toReal * ((historyKL P Q h).toReal + entropySlope n * _) ≤ _
  change (P (state P Q h).event).toReal * (historyKL P Q h).toReal = _ at he
  unfold entropySlope
  nlinarith

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    historyKL P Q h ≠ ∞ ∧
    (P (state P Q h).event).toReal * historyCost P Q h ≤
      (∫ z in (state P Q h).event,llr P (uniformCell Q) z ∂P) +
        (P (state P Q h).event).toReal * rewardLog P Q (complementReward P) h := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget hn P Q hac hK h hp
    | exact OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget
    | (apply OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget <;> assumption)
