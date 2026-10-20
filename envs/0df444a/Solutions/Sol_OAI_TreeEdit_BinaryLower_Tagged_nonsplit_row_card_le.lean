-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.nonsplit_row_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:29:22.49523+00:00
-- url     : https://prove2.me/submissions/67418133-1ee6-49ad-a67c-570090a0d78b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean:L194-L224
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.nonsplit_row_card_le. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_constant_on_row_fiber

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedGaps ----
namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- A row not counted as split sends all its matches to one target row. -/
theorem target_row_eq_of_not_split {n m B r : ℕ}
    (u v : Fin (n + 1) → ℕ) (hu : Monotone u)
    (hr : r ∉ splitRows m B u v) :
    ∀ i j, u i / B / m = r → u j / B / m = r →
      v i / B / m = v j / B / m := by
  apply constant_on_row_fiber (fun i => u i / B / m) (fun i => v i / B / m)
  · intro i j hij
    exact Nat.div_le_div_right (Nat.div_le_div_right (hu hij))
  · intro i hi hj
    by_contra hne
    apply hr
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.trans hj.symm, hne⟩, hi⟩

/-- Row indices of positions in a `T`-row word are strictly below `T`. -/
theorem row_index_lt {p T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hp : p < T * m * B) : p / B / m < T := by
  apply (Nat.div_lt_iff_lt_mul hm).2
  apply (Nat.div_lt_iff_lt_mul hB).2
  exact hp

/-- Per-row-pair matching bounds apply to every nonsplit source row. Empty
source fibers are included rather than discarded. -/
theorem nonsplit_row_card_le {n T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : Monotone u)
    (hv : ∀ i, v i < T * m * B) (d : ℝ) (hd : d ≤ (m * B : ℕ))
    (hlocal : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin (n + 1) =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d)
    {a : ℕ} (ha : a < T) (haS : a ∉ splitRows m B u v) :
    ((univ.filter fun i : Fin (n + 1) => u i / B / m = a).card : ℝ) ≤
      (m * B : ℕ) - d := by
  classical
  let S := univ.filter fun i : Fin (n + 1) => u i / B / m = a
  change (S.card : ℝ) ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨t, ht⟩ := hS
    have hta : u t / B / m = a := (mem_filter.mp ht).2
    have heq : S = univ.filter fun i : Fin (n + 1) =>
        u i / B / m = a ∧ v i / B / m = v t / B / m := by
      ext i
      simp only [S, mem_filter, mem_univ, true_and]
      constructor
      · intro hi
        exact ⟨hi, target_row_eq_of_not_split u v hu haS i t hi hta⟩
      · exact And.left
    rw [heq]
    exact hlocal a ha _ (row_index_lt hm hB (hv t))
  · have hzero : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    rw [hzero]
    simp only [card_empty, Nat.cast_zero]
    linarith

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.nonsplit_row_card_le := @_root_.OAI.TreeEdit.BinaryLower.Tagged.nonsplit_row_card_le
