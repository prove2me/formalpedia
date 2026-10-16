-- Prove2me | solution 1 for OAI.TreeEdit.FiniteProbability.probability_eq_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:26:32.352896+00:00
-- url     : https://prove2.me/submissions/8a3e4bd0-c39d-42c9-9d9c-805335f05ebd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean:L117-L131
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteProbability.probability_eq_of_uniform. The node keeps its source
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

lemma mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma mean_sum {A I : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma probability_eq_of_uniform {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B) (hf : ∀ b c, probability (fun a => f a = b) = probability (fun a => f a = c))
    (b : B) : probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹ := by
  have hB : Nonempty B := ⟨f (Classical.arbitrary A)⟩
  have hs : (∑ c : B, probability (fun a => f a = c)) = 1 := by
    simp only [probability]
    rw [← mean_sum]
    simpa using mean_const (A := A) (1 : ℝ)
  have he : (∑ c : B, probability (fun a => f a = c)) =
      (Fintype.card B : ℝ) * probability (fun a => f a = b) := by
    conv_lhs => arg 2; ext c; rw [hf c b]
    simp
  rw [he] at hs
  apply mul_left_cancel₀ (show (Fintype.card B : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
  rw [hs, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]

end TreeEdit.FiniteProbability

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteProbability.probability_eq_of_uniform := @_root_.OAI.TreeEdit.FiniteProbability.probability_eq_of_uniform
