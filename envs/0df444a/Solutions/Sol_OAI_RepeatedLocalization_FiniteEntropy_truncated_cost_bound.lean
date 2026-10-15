-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:36:39.070917+00:00
-- url     : https://prove2.me/submissions/fc7832c5-2b50-4df4-a68f-a3ad0e2e87ba

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/EntropyBudget.lean:L51-L79
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound. The node keeps its source
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
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_countable_cost_bound
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_historyKL_ne_top_budget
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_run
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_run_eq_iff_mem
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

lemma run_fiber_ae_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    {w | run P Q N w = run P Q N z} =ᵐ[P] (state P Q (run P Q N z)).event := by
  filter_upwards [hroot] with w hw
  exact propext (run_eq_iff_mem hn P Q N hz hw)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.CountableIntegrals ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma integral_comp_fiber {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ι) (F : ι → ℝ) (i : ι) (hi : MeasurableSet {x | L x = i}) :
    (∫ x in {x | L x = i},F (L x) ∂μ) = (μ {x | L x = i}).toReal * F i := by
  rw [setIntegral_congr_fun hi (fun x hx => congrArg F hx)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.RewardBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma exists_run_fiber_root {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) (h : Log n)
    (hp : P {z | run P Q N z = h} ≠ 0) :
    ∃ z,z ∈ cellSet Q ∧ run P Q N z = h := by
  have he : ({z | run P Q N z = h} ∩ cellSet Q : Set (Coordinate n)) =ᵐ[P] {z | run P Q N z = h} := by
    filter_upwards [hroot] with z hz
    change (run P Q N z = h ∧ z ∈ cellSet Q) = (run P Q N z = h)
    simp only [hz,and_true]
  have hp' : P ({z | run P Q N z = h} ∩ cellSet Q) ≠ 0 := by
    rw [measure_congr he]; exact hp
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hp'
  exact ⟨z,hz.2,hz.1⟩

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.EntropyBudget ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma historyCost_nonneg {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    0 ≤ historyCost P Q h := by
  unfold historyCost entropySlope
  exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) (by norm_num)) (Nat.cast_nonneg _))

lemma truncated_cost_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => historyCost P Q (run P Q N z)) P ∧
    (∫ z,historyCost P Q (run P Q N z) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + ∫ z,complementTotal P Q N z ∂P := by
  let := uniformCell_probability hn Q
  have hroot := ae_mem_cell_of_ac hac
  have hi := (InformationTheory.klDiv_ne_top_iff.mp hK).2
  have hJ := (truncated_reward_bounds hn P Q hroot N).1
  have hb (h : Log n) : (P {z | run P Q N z = h}).toReal * historyCost P Q h ≤
      ∫ z in {z | run P Q N z = h},llr P (uniformCell Q) z + complementTotal P Q N z ∂P := by
    by_cases hp : P {z | run P Q N z = h} = 0
    · rw [hp,ENNReal.toReal_zero,zero_mul,Measure.restrict_eq_zero.mpr hp,integral_zero_measure]
    obtain ⟨z,hz,hzh⟩ := exists_run_fiber_root P Q hroot N h hp
    have he : {w | run P Q N w = h} =ᵐ[P] (state P Q h).event := by
      simpa only [hzh] using run_fiber_ae_event hn P Q hroot N hz
    have hp' : P (state P Q h).event ≠ 0 := by rwa [← measure_congr he]
    have hb := (historyKL_ne_top_budget hn P Q hac hK h hp').2
    rw [integral_add hi.integrableOn hJ.integrableOn]
    change _ ≤ (∫ z in {z | run P Q N z = h},llr P (uniformCell Q) z ∂P) +
      ∫ z in {z | run P Q N z = h},(fun h => rewardLog P Q (complementReward P) h) (run P Q N z) ∂P
    rw [integral_comp_fiber P (run P Q N) (rewardLog P Q (complementReward P)) h
      ((measurable_run hn P Q N) (measurableSet_singleton h)),Measure.restrict_congr_set he,measure_congr he]
    exact hb
  have hb' := countable_cost_bound P (run P Q N) (measurable_run hn P Q N)
    (historyCost P Q) (historyCost_nonneg P Q) (hi.add hJ) hb
  simp only [Pi.add_apply] at hb'
  rw [integral_add hi hJ,← InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)] at hb'
  exact hb'

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => historyCost P Q (run P Q N z)) P ∧
    (∫ z,historyCost P Q (run P Q N z) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + ∫ z,complementTotal P Q N z ∂P := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound hn P Q hac hK N
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound
    | (apply OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound <;> assumption)
