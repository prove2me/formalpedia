-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:14:52.497972+00:00
-- url     : https://prove2.me/submissions/78f8f755-517b-45fe-b9d4-39633cb2c6b0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L103-L120
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma state_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    state P Q (h++[a]) = update P (state P Q h) a := by
  simp only [state,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma state_event_subset_cell {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    (state P Q h).event ⊆ cellSet (state P Q h).cell := by
  classical
  induction h using List.reverseRecOn with
  | nil => exact Subset.rfl
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · cases a with
      | none => exact Set.inter_subset_left.trans ih
      | some R =>
        simp only [Option.getD_some]
        intro z hz
        by_cases hR : FirstHeavy (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell R
        · simpa only [branch,ite_eq_left hR] using hz.2
        · simpa only [branch,ite_eq_right hR,Set.mem_empty_iff_false] using hz.2

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    (state P Q h).event ⊆ cellSet (state P Q h).cell := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell P Q h
    | exact OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell
    | (apply OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell <;> assumption)
