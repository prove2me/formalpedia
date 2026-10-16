-- Prove2me | solution 1 for OAI.TreeEdit.FiniteProbability.hom_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:29:09.576862+00:00
-- url     : https://prove2.me/submissions/07fed575-fd1d-460f-b08c-c0030b544a5d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean:L232-L246
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteProbability.hom_uniform. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_probability_eq_of_uniform

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  simp only [mean, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

lemma hom_uniform {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹ := by
  apply probability_eq_of_uniform
  intro b c
  obtain ⟨x, hx⟩ := hf (c - b)
  let e : A ≃ A := Equiv.addLeft x
  have he (a : A) : f (e a) = c ↔ f a = b := by
    change f (x + a) = c ↔ f a = b
    rw [map_add, hx]
    constructor <;> intro h
    · exact add_left_cancel (h.trans (sub_add_cancel c b).symm)
    · rw [h, sub_add_cancel]
  have hh := mean_equiv e (fun a => if f a = c then (1 : ℝ) else 0)
  simpa only [he, probability] using hh

end TreeEdit.FiniteProbability

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteProbability.hom_uniform := @_root_.OAI.TreeEdit.FiniteProbability.hom_uniform
