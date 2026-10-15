-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.terminal_regular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:47:16.349412+00:00
-- url     : https://prove2.me/submissions/a2d92c0c-cbce-4d90-ab15-a39b9470a481

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Termination.lean:L163-L184
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.terminal_regular. The node keeps its source
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
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_almost_sure_termination
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_historyKL_ne_top_budget
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_descendant_of_mem
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_stopped_regular
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminalLog_fiber_inter_initial

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
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
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

lemma attempts_spec {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (state P Q (terminalLog P Q z)).stopped = true := by
  simpa only [terminalLog,attempts,dite_eq_left hz] using Nat.find_spec hz

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

lemma state_event_append_subset {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    (state P Q (h++[a])).event ⊆ (state P Q h).event := by
  rw [state_append]
  unfold update
  split
  · exact Subset.rfl
  · exact Set.inter_subset_left

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

lemma exists_fiber_good {α ι : Type*} [MeasurableSpace α] (P : Measure α) (L : α → ι)
    (Good : α → Prop) (hgood : ∀ᵐ z ∂P,Good z) (i : ι) (hp : P {z | L z = i} ≠ 0) :
    ∃ z,L z = i ∧ Good z := by
  classical
  by_contra h
  have ha : ∀ᵐ z ∂P,L z ≠ i := hgood.mono (fun z hz he => h ⟨z,he,hz⟩)
  exact hp (by simpa only [not_not] using (ae_iff.mp ha))

lemma history_regular_of_stopped {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (Q : Cell n) (h : Log n) (hp : P (state P Q h).event ≠ 0) (hs : (state P Q h).stopped = true) :
    Regular (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell := by
  induction h using List.reverseRecOn with
  | nil => simp only [state_nil,Bool.false_eq_true] at hs
  | append_singleton h a ih =>
    have hp0 : P (state P Q h).event ≠ 0 := by
      intro he
      exact hp (measure_mono_null (state_event_append_subset P Q h a) he)
    by_cases hs0 : (state P Q h).stopped = true
    · simp only [state_append,update,hs0,ite_true] at hs ⊢
      exact ih hp0 hs0
    let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hp0
    cases a with
    | some R => simp [state_append,update,hs0] at hs
    | none =>
      have hq : (1/2:ℝ) ≤ ((ProbabilityTheory.cond P (state P Q h).event)
          (residual (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell)).toReal := by
        simpa [state_append,update,hs0,branch] using hs
      have hr := stopped_regular hn (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell hq
      rw [ProbabilityTheory.cond_cond_eq_cond_inter' (state_event_measurable P Q h)
        (measurableSet_residual _ _) (measure_ne_top _ _)] at hr
      simpa [state_append,update,hs0,branch] using hr

lemma terminal_regular {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P {z | terminalLog P Q z = h} ≠ 0) :
    Descendant Q (terminalCell P Q h) ∧ Regular (terminalLaw P Q h) (terminalCell P Q h) ∧
      InformationTheory.klDiv (terminalLaw P Q h) (uniformCell (terminalCell P Q h)) ≠ ∞ := by
  have hn0 : 0 < n := by omega
  have hroot := ae_mem_cell_of_ac hac
  have hterm := almost_sure_termination hn P Q hac hK
  obtain ⟨z,hzh,hz,ht⟩ := exists_fiber_good P (terminalLog P Q)
    (fun z => z ∈ cellSet Q ∧ Terminates P Q z) (hroot.and hterm) h hp
  have he : {w | terminalLog P Q w = h} =ᵐ[P] (state P Q h).event := by
    simpa only [hzh] using terminal_fiber_ae_event hn0 P Q hroot hz ht
  have hp' : P (state P Q h).event ≠ 0 := by rwa [← measure_congr he]
  have hstop : (state P Q h).stopped = true := by
    rw [← hzh]
    exact attempts_spec P Q ht
  have hLaw : terminalLaw P Q h = ProbabilityTheory.cond P (state P Q h).event := cond_congr_ae P he
  refine ⟨positive_event_descendant P Q h hp',?_,?_⟩
  · rw [hLaw]
    exact history_regular_of_stopped hn0 P Q h hp' hstop
  · rw [hLaw]
    exact (historyKL_ne_top_budget hn0 P Q hac hK h hp').1

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
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P {z | terminalLog P Q z = h} ≠ 0) :
    Descendant Q (terminalCell P Q h) ∧ Regular (terminalLaw P Q h) (terminalCell P Q h) ∧
      InformationTheory.klDiv (terminalLaw P Q h) (uniformCell (terminalCell P Q h)) ≠ ∞ := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.terminal_regular hn P Q hac hK h hp
    | exact OAI.RepeatedLocalization.FiniteEntropy.terminal_regular
    | (apply OAI.RepeatedLocalization.FiniteEntropy.terminal_regular <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.terminal_regular <;> assumption)
