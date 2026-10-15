-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.state_descendant_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:16:14.059186+00:00
-- url     : https://prove2.me/submissions/bbd6cc15-6a3d-452b-824d-07cab5bc4059

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L122-L141
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.state_descendant_of_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

-- ---- from OAI.Probability.Localization.FirstHeavy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma Descendant.refl {n : ℕ} (Q : Cell n) : Descendant Q Q := ⟨le_rfl,Subset.rfl⟩

lemma Descendant.trans {n : ℕ} {Q R S : Cell n} (hQR : Descendant Q R) (hRS : Descendant R S) :
    Descendant Q S := ⟨hQR.1.trans hRS.1,hRS.2.trans hQR.2⟩

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma state_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    state P Q (h++[a]) = update P (state P Q h) a := by
  simp only [state,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma state_descendant_of_mem {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (h : Log n) {z : Coordinate n} (hz : z ∈ (state P Q h).event) :
    Descendant Q (state P Q h).cell := by
  classical
  induction h using List.reverseRecOn with
  | nil => exact Descendant.refl Q
  | append_singleton h a ih =>
    rw [state_append] at hz ⊢
    unfold update at hz ⊢
    by_cases hs : (state P Q h).stopped = true
    · simp only [hs,ite_true] at hz ⊢
      exact ih hz
    · simp only [hs] at hz ⊢
      cases a with
      | none => exact ih hz.1
      | some R =>
        have hR : FirstHeavy (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell R := by
          by_contra hR
          simpa only [branch,ite_eq_right hR,Set.mem_empty_iff_false] using hz.2
        exact (ih hz.1).trans hR.1.1

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (h : Log n) {z : Coordinate n} (hz : z ∈ (state P Q h).event) :
    Descendant Q (state P Q h).cell := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.state_descendant_of_mem P Q h hz
    | exact OAI.RepeatedLocalization.FiniteEntropy.state_descendant_of_mem
    | (apply OAI.RepeatedLocalization.FiniteEntropy.state_descendant_of_mem <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.state_descendant_of_mem <;> assumption)
