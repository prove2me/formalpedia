-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:49:26.443312+00:00
-- url     : https://prove2.me/submissions/035410fa-668d-4571-9eac-70517179608b

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/TerminalBudget.lean:L32-L56
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget. The node keeps its source
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
import Definitions.Def_OAI_Probability_Localization_TerminalBudget
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_almost_sure_termination
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_frozen_nonnegative_bound
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_attempts
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_run
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminalLog_fiber_inter_initial
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_cost_bound
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_final_budget

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
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma run_succ_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    (z : Coordinate n) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q (N+1) z = run P Q N z := by simp only [run,h,ite_true]

lemma run_add_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N M : ℕ)
    (z : Coordinate n) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q (N+M) z = run P Q N z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.add_succ,run_succ_of_stopped P Q (N+M) z (by rw [ih]; exact h),ih]

lemma run_of_stopped_le {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {N M : ℕ}
    (z : Coordinate n) (hNM : N ≤ M) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q M z = run P Q N z := by
  obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le hNM
  exact run_add_of_stopped P Q N M z h

lemma attempts_spec {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (state P Q (terminalLog P Q z)).stopped = true := by
  simpa only [terminalLog,attempts,dite_eq_left hz] using Nat.find_spec hz

lemma measurable_terminalLog {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (terminalLog P Q) := by
  have hm : Measurable (fun Nz : ℕ × Coordinate n => run P Q Nz.1 Nz.2) :=
    measurable_from_prod_countable_right (measurable_run hn P Q)
  exact hm.comp ((measurable_attempts hn P Q).prodMk measurable_id)

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

lemma cond_congr_ae {α : Type*} [MeasurableSpace α] (P : Measure α) {E F : Set α}
    (h : E =ᵐ[P] F) : ProbabilityTheory.cond P E = ProbabilityTheory.cond P F := by
  unfold ProbabilityTheory.cond
  rw [measure_congr h,Measure.restrict_congr_set h]

lemma terminal_fiber_ae_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    {w | terminalLog P Q w = terminalLog P Q z} =ᵐ[P] (state P Q (terminalLog P Q z)).event := by
  have he := terminalLog_fiber_inter_initial hn P Q hz ht
  filter_upwards [hroot] with w hw
  apply propext
  constructor
  · intro hm
    rw [← he]
    exact ⟨hw,hm⟩
  · intro hm
    rw [← he] at hm
    exact hm.2

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

lemma run_eventually_terminal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (ht : Terminates P Q z) :
    ∀ M,attempts P Q z ≤ M → run P Q M z = terminalLog P Q z := by
  intro M hM
  exact run_of_stopped_le P Q z hM (attempts_spec P Q ht)

lemma budget_nonneg {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    0 ≤ (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by positivity

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.TerminalBudget ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma measurable_terminalKL {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (terminalKL P Q) :=
  (measurable_of_countable (fun h : Log n => InformationTheory.klDiv (terminalLaw P Q h)
    (uniformCell (terminalCell P Q h)))).comp (measurable_terminalLog hn P Q)

lemma measurable_depth_real {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (fun z => (depth P Q z:ℝ)) :=
  (measurable_of_countable (fun h : Log n => (((terminalCell P Q h).1-Q.1:ℕ):ℝ))).comp
    (measurable_terminalLog hn P Q)

lemma terminal_historyKL {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    terminalKL P Q z = historyKL P Q (terminalLog P Q z) := by
  unfold terminalKL historyKL terminalLaw terminalCell
  rw [cond_congr_ae P (terminal_fiber_ae_event hn P Q hroot hz ht)]

lemma terminal_cost_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ)) P ∧
      (∫ z,(terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ) ∂P) ≤
        (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by
  have hn0 : 0 < n := by omega
  have hs : 0 ≤ entropySlope n/2 := le_of_lt (div_pos (entropySlope_pos hn0) (by norm_num))
  apply frozen_nonnegative_bound P
    (fun N z => (historyKL P Q (run P Q N z)).toReal + entropySlope n/2*(truncatedDepth P Q N z:ℝ))
    _ _ (budget_nonneg P Q)
  · intro N
    exact (truncated_KL_integrable hn0 P Q hac hK N).add
      ((truncated_depth_integrable hn0 P Q hac hK N).const_mul _)
  · intro N z
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hs (Nat.cast_nonneg _))
  · exact ((measurable_terminalKL hn0 P Q).ennreal_toReal.add
      ((measurable_depth_real hn0 P Q).const_mul _)).aestronglyMeasurable
  · intro z
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hs (Nat.cast_nonneg _))
  · have hroot := ae_mem_cell_of_ac hac
    filter_upwards [hroot,almost_sure_termination hn P Q hac hK] with z hz ht
    refine ⟨attempts P Q z,fun M hM => ?_⟩
    have he := run_eventually_terminal P Q ht M hM
    simp only [truncatedDepth,he,← terminal_historyKL hn0 P Q hroot hz ht,depth,terminalCell]
  · exact truncated_final_budget hn P Q hac hK

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ)) P ∧
      (∫ z,(terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ) ∂P) ≤
        (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget hn P Q hac hK
    | exact OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget
    | (apply OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget <;> assumption)
