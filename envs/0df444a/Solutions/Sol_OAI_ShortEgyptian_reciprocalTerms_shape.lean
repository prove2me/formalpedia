-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocalTerms_shape
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:14:01.995332+00:00
-- url     : https://prove2.me/submissions/915a74c5-2af9-4ef0-812e-1bf128c05f8b

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ReciprocalDifferences.lean:L92-L118
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocalTerms_shape. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences

-- ---- from OAI.NumberTheory.ShortEgyptian.ReciprocalDifferences ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem expandDifference_shape {h H : ℝ} (hh : 0 ≤ h)
    (as : List ℝ) (has : ∀ a ∈ as, 0 ≤ a ∧ a ≤ H) :
    ∀ bs ∈ expandDifference h as,
      bs.length = as.length + 1 ∧ ∀ b ∈ bs, 0 ≤ b ∧ b ≤ H + h := by
  induction as with
  | nil => simp [expandDifference]
  | cons a as ih =>
    intro bs hbs
    have ha := has a (by simp)
    have has' : ∀ b ∈ as, 0 ≤ b ∧ b ≤ H := fun b hb => has b (by simp [hb])
    simp only [expandDifference, List.mem_cons] at hbs
    rcases hbs with rfl | hbs
    · refine ⟨by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.mem_map] at hb
      rcases hb with rfl | rfl | ⟨c, hc, rfl⟩
      · exact ⟨ha.1, by linarith [ha.2]⟩
      · exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
      · exact ⟨by linarith [(has' c hc).1], by linarith [(has' c hc).2]⟩
    · obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hbs
      obtain ⟨hcl, hcp⟩ := ih has' cs hcs
      refine ⟨by simp [hcl], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨ha.1, by linarith [ha.2]⟩
      · exact hcp b hb

theorem reciprocalTerms_shape (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) :
    (reciprocalTerms hs).length = hs.length.factorial ∧
      ∀ as ∈ reciprocalTerms hs,
        as.length = hs.length + 1 ∧ ∀ a ∈ as, 0 ≤ a ∧ a ≤ hs.sum := by
  induction hs with
  | nil => simp [reciprocalTerms]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (by simp)
    have hhs' : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    obtain ⟨hlen, hshape⟩ := ih hhs'
    constructor
    · simp only [reciprocalTerms, List.length_flatMap, expandDifference_length]
      have heq : ((reciprocalTerms hs).map List.length) =
          (reciprocalTerms hs).map (fun _ => hs.length + 1) := by
        apply List.map_congr_left
        intro as has
        exact (hshape as has).1
      rw [heq]
      simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, hlen, List.length_cons, Nat.factorial_succ]
      exact Nat.mul_comm _ _
    · intro as has
      obtain ⟨bs, hbs, has⟩ := List.mem_flatMap.mp has
      obtain ⟨hbsl, hbsp⟩ := hshape bs hbs
      obtain ⟨hasl, hasp⟩ := expandDifference_shape hh bs hbsp as has
      refine ⟨by simpa [hbsl] using hasl, ?_⟩
      intro a ha
      simpa only [List.sum_cons, add_comm] using hasp a ha

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocalTerms_shape := @_root_.OAI.ShortEgyptian.reciprocalTerms_shape
