-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.matched_split_gain_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:39:32.853698+00:00
-- url     : https://prove2.me/submissions/f31b5661-d7f3-42c5-a5e1-8a53d9c58eb0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L275-L313
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.matched_split_gain_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_split_gain_le
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_sum_extend_zero

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma ancestral_not_above (c : ι) : A.Ancestral {v | ¬ c ≤ v} := by
  intro a b hab hb ha
  exact hb (ha.trans hab)

/-- Simultaneous splitting restricted to any injected list of original segments. -/
lemma matched_split_gain_le {κ : Type*} [Fintype κ]
    (F : A.segments.Family) (e : κ ↪ Fin F.n) (c : κ → ι) (p : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      2 * (∑ a, ((∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
        (∑ v ∈ F.seg (e a), p v) *
          (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v))) ≤
      (A.segments.primalSeminorm p) ^ 2 := by
  classical
  let H : Fin F.n → Set ι := Function.extend e (fun a => {v | ¬ c a ≤ v}) (fun _ => Set.univ)
  have he (a : κ) : H (e a) = {v | ¬ c a ≤ v} := e.injective.extend_apply _ _ _
  have hout (i : Fin F.n) (hi : ¬ ∃ a, e a = i) : H i = Set.univ :=
    Function.extend_apply' _ _ _ hi
  have hH : ∀ i, A.Ancestral (H i) := by
    intro i
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [he]
      exact A.ancestral_not_above (c a)
    · rw [hout i hi]
      intro a b _ _
      trivial
  have hb := A.split_gain_le F H hH p
  let q : κ → ℝ := fun a =>
    (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
      (∑ v ∈ F.seg (e a), p v) *
        (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v)
  have hid : (fun i => (∑ v ∈ (F.seg i).filter (· ∉ H i), p v) ^ 2 -
      (∑ v ∈ F.seg i, p v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), p v)) =
        Function.extend e q (fun _ => 0) := by
    funext i
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [he, e.injective.extend_apply]
      simp [q]
    · rw [hout i hi, Function.extend_apply' _ _ _ hi]
      simp
  rw [hid, sum_extend_zero] at hb
  exact hb

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.matched_split_gain_le := @_root_.OAI.DiamondDistortion.Ancestry.matched_split_gain_le
