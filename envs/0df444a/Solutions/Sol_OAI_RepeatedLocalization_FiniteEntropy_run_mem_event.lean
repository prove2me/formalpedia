-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.run_mem_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:18:52.408587+00:00
-- url     : https://prove2.me/submissions/0ab38270-c392-446f-a861-af67d932a5f9

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L183-L195
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.run_mem_event. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_event_subset_cell

-- ---- from OAI.Probability.Localization.FirstHeavy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma attemptLetter_mem_branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : z ∈ branch P Q (attemptLetter P Q z) := by
  classical
  by_cases h : ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R
  · simp only [attemptLetter,dite_eq_left h,branch,ite_eq_left h.choose_spec.1]
    exact h.choose_spec.2
  · simp only [attemptLetter,dite_eq_right h,branch,residual]
    refine ⟨hz,?_⟩
    intro hm
    obtain ⟨R,hR⟩ := Set.mem_iUnion.mp hm
    exact h ⟨R.val,R.property,hR⟩

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

lemma run_mem_event {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : z ∈ (state P Q (run P Q N z)).event := by
  induction N with
  | zero => exact hz
  | succ N ih =>
    simp only [run]
    split
    · exact ih
    · rw [state_append]
      unfold update
      split
      · exact ih
      · exact ⟨ih,attemptLetter_mem_branch _ _ (state_event_subset_cell _ _ _ ih)⟩

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : z ∈ (state P Q (run P Q N z)).event := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.run_mem_event P Q N hz
    | exact OAI.RepeatedLocalization.FiniteEntropy.run_mem_event
    | (apply OAI.RepeatedLocalization.FiniteEntropy.run_mem_event <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.run_mem_event <;> assumption)
