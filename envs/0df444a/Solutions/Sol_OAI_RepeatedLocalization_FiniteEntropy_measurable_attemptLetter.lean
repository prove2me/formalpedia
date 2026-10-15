-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:13:36.711233+00:00
-- url     : https://prove2.me/submissions/1ee9cc20-66e0-4090-8ed9-e4690dfc7838

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L55-L79
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_attemptLetter_some_iff

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
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma attemptLetter_none_iff {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) :
    attemptLetter P Q z = none ↔ ¬ ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R := by
  classical
  by_cases h : ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R
  · rw [attemptLetter,dite_eq_left h]
    simp only [reduceCtorEq,h,not_true_eq_false]
  · rw [attemptLetter,dite_eq_right h]
    simp only [h,not_false_eq_true]

lemma measurableSet_firstHeavy_union {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet (⋃ R : {R : Cell n // FirstHeavy P Q R},cellSet R.val) :=
  MeasurableSet.iUnion fun R => measurableSet_cellSet R.val

lemma measurable_attemptLetter {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attemptLetter P Q) := by
  classical
  apply measurable_to_countable'
  intro a
  change MeasurableSet {z | attemptLetter P Q z = a}
  cases a with
  | none =>
    have he : {z | attemptLetter P Q z = none} =
        (⋃ R : {R : Cell n // FirstHeavy P Q R},cellSet R.val)ᶜ := by
      ext z
      simp only [Set.mem_ofPred_eq,attemptLetter_none_iff,Set.mem_compl_iff,Set.mem_iUnion]
      apply not_congr
      exact ⟨fun ⟨R,hR,hzR⟩ => ⟨⟨R,hR⟩,hzR⟩,fun ⟨R,hzR⟩ => ⟨R.val,R.property,hzR⟩⟩
    rw [he]
    exact (measurableSet_firstHeavy_union P Q).compl
  | some R =>
    have he : {z | attemptLetter P Q z = some R} = {z | FirstHeavy P Q R ∧ z ∈ cellSet R} := by
      ext z
      exact attemptLetter_some_iff hn P Q R z
    rw [he]
    by_cases hR : FirstHeavy P Q R
    · convert measurableSet_cellSet R using 1
      ext z; simp only [Set.mem_ofPred_eq,hR,true_and]
    · simp only [hR,false_and,Set.ofPred_false,MeasurableSet.empty]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attemptLetter P Q) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter hn P Q
    | exact OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter
    | (apply OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter <;> assumption)
