-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.split_rows_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:31:18.847218+00:00
-- url     : https://prove2.me/submissions/fd5d74a9-4332-4b01-bcc9-4c900d8437cb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean:L226-L256
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.split_rows_gap_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_selected_gap_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_tagged_gap

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedGaps ----
namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- The split-row inequality, with no restriction on how many times
a source row crosses target rows. -/
theorem split_rows_gap_bound {n N m B : ℕ} (hm : 1 ≤ m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hN : ∀ i, v i < N)
    (htags : ∀ i, (u i / B) % m = (v i / B) % m) :
    ((splitRows m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) ≤
      (N : ℝ) - (n + 1) := by
  have hgap (i : Fin n) (hi : i ∈ splitTransitions m B u v) :
      ((((m - 1) * B : ℕ) : ℝ)) ≤
        (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1 := by
    have hpair := (mem_filter.1 hi).2
    have hij : i.castSucc < i.succ := by simp
    have hvrow : v i.castSucc / B / m < v i.succ / B / m := by
      have hle : v i.castSucc / B / m ≤ v i.succ / B / m :=
        Nat.div_le_div_right (Nat.div_le_div_right (hv.monotone (le_of_lt hij)))
      exact lt_of_le_of_ne hle hpair.2
    have h := tagged_gap hm hB (hu.monotone (le_of_lt hij))
      hpair.1 hvrow (htags i.castSucc) (htags i.succ)
    have hc : (v i.castSucc : ℝ) + 1 + (((m - 1) * B : ℕ) : ℝ) ≤
        (v i.succ : ℝ) := by exact_mod_cast h
    linarith
  have hcount : (splitRows m B u v).card ≤ (splitTransitions m B u v).card :=
    card_image_le
  calc
    ((splitRows m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) ≤
        ((splitTransitions m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hcount
    _ ≤ (N : ℝ) - (n + 1) :=
      selected_gap_bound v hv hN (splitTransitions m B u v) _ hgap

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.split_rows_gap_bound := @_root_.OAI.TreeEdit.BinaryLower.Tagged.split_rows_gap_bound
