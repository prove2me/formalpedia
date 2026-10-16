-- Prove2me | solution 1 for OAI.TreeEdit.FiniteProbability.probability_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:23:29.595837+00:00
-- url     : https://prove2.me/submissions/6ce48c0a-8369-4478-a1eb-f1ae60f255e2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean:L76-L89
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteProbability.probability_union_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_sum {A I : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma probability_union_bound {A I : Type*} [Fintype A] (s : Finset I) (E : I → A → Prop) :
    probability (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, probability (E i) := by
  classical
  simp only [probability]
  rw [← mean_sum]
  apply mean_le
  intro a
  split_ifs with h
  · obtain ⟨i, hi, he⟩ := h
    calc
      (1 : ℝ) = (if E i a then (1 : ℝ) else 0) := by simp [he]
      _ ≤ ∑ j ∈ s, (if E j a then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun j => if E j a then (1 : ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) hi
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

end TreeEdit.FiniteProbability

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteProbability.probability_union_bound := @_root_.OAI.TreeEdit.FiniteProbability.probability_union_bound
