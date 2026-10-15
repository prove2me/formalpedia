-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.measurable_attempts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:21:37.961178+00:00
-- url     : https://prove2.me/submissions/adc0c7df-db98-462b-b512-74e645097113

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L324-L347
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.measurable_attempts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_run

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

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

lemma measurable_attempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attempts P Q) := by
  classical
  have hex (z : Coordinate n) : ∃ N : ℕ,(state P Q (run P Q N z)).stopped = true ∨ ¬ Terminates P Q z := by
    by_cases h : Terminates P Q z
    · obtain ⟨N,hN⟩ := h
      exact ⟨N,Or.inl hN⟩
    · exact ⟨0,Or.inr h⟩
  have he (z : Coordinate n) : attempts P Q z = Nat.find (hex z) := by
    by_cases h : Terminates P Q z
    · simp only [attempts,dite_eq_left h]
      apply le_antisymm
      · exact Nat.find_min' h ((Nat.find_spec (hex z)).resolve_right (not_not.mpr h))
      · exact Nat.find_min' (hex z) (Or.inl (Nat.find_spec h))
    · simp only [attempts,dite_eq_right h]
      exact (Nat.eq_zero_of_le_zero (Nat.find_min' (hex z) (show
        (state P Q (run P Q 0 z)).stopped = true ∨ ¬ Terminates P Q z from Or.inr h))).symm
  have hm : Measurable (fun z => Nat.find (hex z)) := Measurable.find (f := fun N (_ : Coordinate n) => N) (p := fun N z =>
      (state P Q (run P Q N z)).stopped = true ∨ ¬ Terminates P Q z)
    (fun N => measurable_const) (fun N => (measurableSet_stopped hn P Q N).union
      (measurableSet_terminates hn P Q).compl) hex
  convert hm using 1
  funext z
  exact he z

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attempts P Q) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.measurable_attempts hn P Q
    | exact OAI.RepeatedLocalization.FiniteEntropy.measurable_attempts
    | (apply OAI.RepeatedLocalization.FiniteEntropy.measurable_attempts <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.measurable_attempts <;> assumption)
