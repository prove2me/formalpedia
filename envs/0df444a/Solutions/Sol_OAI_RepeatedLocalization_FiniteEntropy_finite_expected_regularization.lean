-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.finite_expected_regularization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:51:04.959661+00:00
-- url     : https://prove2.me/submissions/619f58c0-c71c-411d-9de1-dc34706355bf

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Main.lean:L12-L22
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.RepeatedLocalization.FiniteEntropy.finite_expected_regularization.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_finite_expected_regularization) verbatim and is proved by it.
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
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminal_cost_budget
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminal_regular
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncatedDepth_mono
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_attempts_integral
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_cost_bound

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

lemma state_nil {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    state P Q [] = ⟨Q,cellSet Q,false⟩ := rfl

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

lemma attempts_min {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) {N : ℕ} (hN : N < attempts P Q z) :
    (state P Q (run P Q N z)).stopped = false := by
  have hm : ¬ (state P Q (run P Q N z)).stopped = true := Nat.find_min hz (by
    simpa only [attempts,dite_eq_left hz] using hN)
  simpa using hm

lemma attempts_pos {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : 0 < attempts P Q z := by
  by_contra h
  have he : attempts P Q z = 0 := by omega
  have hs := attempts_spec P Q hz
  simp [terminalLog,he,run,state_nil] at hs

lemma terminalLog_length {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (terminalLog P Q z).length = attempts P Q z := by
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (attempts_pos P Q hz))
  have hn : (state P Q (run P Q N z)).stopped = false := attempts_min P Q hz (by omega)
  simp only [terminalLog,hN,run,hn,Bool.false_eq_true,ite_false,List.length_append,List.length_singleton]
  rw [run_length_of_active P Q N z hn]

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

lemma ae_fiber_positive {α ι : Type*} [MeasurableSpace α] [Countable ι] (P : Measure α) (L : α → ι) :
    ∀ᵐ z ∂P,P {w | L w = L z} ≠ 0 := by
  classical
  have h (i : ι) : ∀ᵐ z ∂P,L z = i → P {w | L w = i} ≠ 0 := by
    by_cases hp : P {w | L w = i} = 0
    · have ha : ∀ᵐ z ∂P,L z ≠ i := ae_iff.mpr (by simpa only [not_not] using hp)
      exact ha.mono (fun z hz he => (hz he).elim)
    · exact ae_of_all _ (fun _ _ => hp)
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact hz (L z) rfl

lemma run_eventually_terminal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (ht : Terminates P Q z) :
    ∀ M,attempts P Q z ≤ M → run P Q M z = terminalLog P Q z := by
  intro M hM
  exact run_of_stopped_le P Q z hM (attempts_spec P Q ht)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.TerminalBudget ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma measurable_depth_real {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (fun z => (depth P Q z:ℝ)) :=
  (measurable_of_countable (fun h : Log n => (((terminalCell P Q h).1-Q.1:ℕ):ℝ))).comp
    (measurable_terminalLog hn P Q)

lemma terminal_depth_integrable {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (depth P Q z:ℝ)) P := by
  have hn0 : 0 < n := by omega
  have hc := (terminal_cost_budget hn P Q hac hK).1
  apply Integrable.mono' (hc.div_const (entropySlope n/2)) (measurable_depth_real hn0 P Q).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),le_div_iff₀ (div_pos (entropySlope_pos hn0) (by norm_num))]
  nlinarith [ENNReal.toReal_nonneg (a := terminalKL P Q z)]

lemma terminal_KL_integrable {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (terminalKL P Q z).toReal) P := by
  have hc := (terminal_cost_budget hn P Q hac hK).1
  have hd := terminal_depth_integrable hn P Q hac hK
  simpa only [add_sub_cancel_right] using
    hc.sub' (hd.const_mul (entropySlope n/2))

lemma terminal_attempts_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (attempts P Q z:ℝ)) P ∧
      (∫ z,(attempts P Q z:ℝ) ∂P) ≤ 2*(1+∫ z,(depth P Q z:ℝ) ∂P) := by
  have hn0 : 0 < n := by omega
  have hroot := ae_mem_cell_of_ac hac
  have hterm := almost_sure_termination hn P Q hac hK
  have hd := terminal_depth_integrable hn P Q hac hK
  apply frozen_nonnegative_bound P (fun N z => (truncatedAttempts P Q N z:ℝ)) _ _
  · positivity
  · exact integrable_truncatedAttempts hn0 P Q
  · intro N z
    exact Nat.cast_nonneg _
  · exact ((measurable_of_countable (fun a : ℕ => (a:ℝ))).comp (measurable_attempts hn0 P Q)).aestronglyMeasurable
  · intro z
    exact Nat.cast_nonneg _
  · filter_upwards [hterm] with z ht
    refine ⟨attempts P Q z,fun M hM => ?_⟩
    simp only [truncatedAttempts,run_eventually_terminal P Q ht M hM,terminalLog_length P Q ht]
  · intro N
    have he : ∀ᵐ z ∂P,(truncatedDepth P Q N z:ℝ) ≤ (depth P Q z:ℝ) := by
      filter_upwards [hroot,hterm] with z hz ht
      have hm := truncatedDepth_mono hn0 P Q hz (Nat.le_max_left N (attempts P Q z))
      have hf := run_eventually_terminal P Q ht (max N (attempts P Q z)) (Nat.le_max_right _ _)
      simp only [truncatedDepth,hf] at hm
      exact_mod_cast hm
    have hi := integral_mono_ae (truncated_depth_integrable hn0 P Q hac hK N) hd he
    exact (truncated_attempts_integral hn0 P Q hac hK N).trans (by linarith)

lemma terminal_ennreal_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    (∫⁻ z,terminalKL P Q z ∂P) + ENNReal.ofReal ((Real.log 2/4)*n*(∫ z,(depth P Q z:ℝ) ∂P)) ≤
      InformationTheory.klDiv P (uniformCell Q) + ENNReal.ofReal (2/Real.exp 1) := by
  have hd := terminal_depth_integrable hn P Q hac hK
  have hk := terminal_KL_integrable hn P Q hac hK
  have hc := (terminal_cost_budget hn P Q hac hK).2
  rw [integral_add hk (hd.const_mul _),integral_const_mul] at hc
  have hfin : ∀ᵐ z ∂P,terminalKL P Q z ≠ ∞ := by
    filter_upwards [ae_fiber_positive P (terminalLog P Q)] with z hz
    exact (terminal_regular hn P Q hac hK (terminalLog P Q z) hz).2.2
  have he : (∫⁻ z,terminalKL P Q z ∂P) = ENNReal.ofReal (∫ z,(terminalKL P Q z).toReal ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))]
    exact lintegral_congr_ae (hfin.mono (fun z hz => (ENNReal.ofReal_toReal hz).symm))
  have hs : (Real.log 2/4)*(n:ℝ) = entropySlope n/2 := by unfold entropySlope; ring
  rw [he,hs,← ENNReal.ofReal_add (integral_nonneg (fun _ => ENNReal.toReal_nonneg))]
  calc
    _ ≤ ENNReal.ofReal ((InformationTheory.klDiv P (uniformCell Q)).toReal+2/Real.exp 1) := ENNReal.ofReal_le_ofReal hc
    _ = _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hK]
      positivity
  · exact mul_nonneg (le_of_lt (div_pos (entropySlope_pos (by omega)) (by norm_num)))
      (integral_nonneg (fun _ => Nat.cast_nonneg _))

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Main ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

theorem finite_expected_regularization : FiniteEntropyStatement := by
  refine ⟨32,fun n hn Q P hP hac hK => ?_⟩
  let := hP
  have hn0 : 0 < n := by omega
  refine ⟨almost_sure_termination hn P Q hac hK,measurable_terminalLog hn0 P Q,?_,
    terminal_depth_integrable hn P Q hac hK,?_,?_,?_⟩
  · intro h hp
    exact ⟨(terminal_regular hn P Q hac hK h hp).1,(terminal_regular hn P Q hac hK h hp).2.1⟩
  · exact (terminal_attempts_budget hn P Q hac hK).1
  · exact (terminal_attempts_budget hn P Q hac hK).2
  · exact terminal_ennreal_budget hn P Q hac hK

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- mission target ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution : FiniteEntropyStatement := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.finite_expected_regularization
    | (apply OAI.RepeatedLocalization.FiniteEntropy.finite_expected_regularization <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.finite_expected_regularization <;> assumption)
