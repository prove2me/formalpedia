-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.BlockRestriction.card_le_lcs_slices
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:37:30.21938+00:00
-- url     : https://prove2.me/submissions/d0b93a29-acf4-4942-8da3-59c983ab0e5f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/BlockRestriction.lean:L15-L59
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.BlockRestriction.card_le_lcs_slices. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSublist ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Strictly increasing index selections produce sublists. -/
theorem ofFn_get_sublist {α : Type*} (x : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (hi : StrictMono i) :
    (List.ofFn (fun t => x.get (i t))).Sublist x := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  let f : Fin (List.ofFn (fun t => x.get (i t))).length → Fin x.length :=
    fun t => i ⟨t, by simpa using t.isLt⟩
  have hf : StrictMono f := fun _ _ h => hi h
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro t
  simp [f]

/-- A matching described by two increasing index maps is a common sublist
with exactly as many symbols as matched index pairs. -/
theorem common_sublist_of_strict_matching {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t)) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k := by
  refine ⟨List.ofFn (fun t => x.get (i t)), ofFn_get_sublist x i hi, ?_, by simp⟩
  have heq : (fun t => x.get (i t)) = (fun t => y.get (j t)) := funext hlabel
  rw [heq]
  exact ofFn_get_sublist y j hj

/-- Every increasing matching has size at most the longest common subsequence. -/
theorem matching_length_le_lcs {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t)) : k ≤ lcs x y := by
  obtain ⟨z, hzx, hzy, hz⟩ := common_sublist_of_strict_matching x y i j hi hj hlabel
  rw [← hz]
  exact length_le_lcs hzx hzy

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.BlockRestriction ----
namespace OAI

/-! Restricting increasing common matchings to arbitrary contiguous intervals. -/

namespace TreeEdit.BinaryLower
namespace BlockRestriction

universe u
variable {α : Type u}

/-- Restriction to any selected set of matched pairs lying in two specified
intervals has size at most the LCS of the corresponding list slices.
The intervals may touch or exceed the list boundary; no artificial positivity
or nonempty-matching assumption is needed. -/
theorem card_le_lcs_slices (x y : List α) {n : ℕ}
    (u v : Fin n → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hxu : ∀ t, u t < x.length) (hyv : ∀ t, v t < y.length)
    (heq : ∀ t, x[u t]'(hxu t) = y[v t]'(hyv t))
    (s : Finset (Fin n)) (a b A B : ℕ)
    (hsu : ∀ t ∈ s, a ≤ u t ∧ u t < a + A)
    (hsv : ∀ t ∈ s, b ≤ v t ∧ v t < b + B) :
    s.card ≤ lcs ((x.drop a).take A) ((y.drop b).take B) := by
  let e : Fin s.card ↪o Fin n := s.orderEmbOfFin rfl
  have he (i : Fin s.card) : e i ∈ s := s.orderEmbOfFin_mem rfl i
  let ui : Fin s.card → Fin ((x.drop a).take A).length := fun i =>
    ⟨u (e i) - a, by
      have h₁ := hsu (e i) (he i)
      have h₂ := hxu (e i)
      simp only [List.length_take, List.length_drop]
      omega⟩
  let vi : Fin s.card → Fin ((y.drop b).take B).length := fun i =>
    ⟨v (e i) - b, by
      have h₁ := hsv (e i) (he i)
      have h₂ := hyv (e i)
      simp only [List.length_take, List.length_drop]
      omega⟩
  have hui : StrictMono ui := by
    intro i j hij
    have hlt := hu (e.strictMono hij)
    have hi := (hsu (e i) (he i)).1
    change u (e i) - a < u (e j) - a
    omega
  have hvi : StrictMono vi := by
    intro i j hij
    have hlt := hv (e.strictMono hij)
    have hi := (hsv (e i) (he i)).1
    change v (e i) - b < v (e j) - b
    omega
  apply TreeEdit.BinaryLower.matching_length_le_lcs _ _ ui vi hui hvi
  intro i
  have hua := (hsu (e i) (he i)).1
  have hvb := (hsv (e i) (he i)).1
  simpa only [ui, vi, List.get_eq_getElem, List.getElem_take,
    List.getElem_drop, Nat.add_sub_of_le hua, Nat.add_sub_of_le hvb]
    using heq (e i)

end BlockRestriction
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.BlockRestriction


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.BlockRestriction.card_le_lcs_slices.{u} := @_root_.OAI.TreeEdit.BinaryLower.BlockRestriction.card_le_lcs_slices.{u}
