-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedExtraction.equal_symbols_same_tag
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:50:20.004897+00:00
-- url     : https://prove2.me/submissions/ccbffb7a-d271-4b97-8cce-1f6a854a640a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedExtraction.lean:L127-L148
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedExtraction.equal_symbols_same_tag. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedExtraction_getElem_blocks

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedExtraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower
namespace TaggedExtraction

universe u
variable {α : Type u}

/-- Indexed extraction of a cell from the literal concatenation of rows. -/
lemma getElem_rows {T m B : ℕ} (X : Fin T → Fin m → Word α B)
    (a : Fin T) (i : Fin m) (j : Fin B) :
    (rows X)[a.val * (m * B) + (i.val * B + j.val)]'
      (by rw [length_rows]; exact row_index_lt a i j) =
      (X a i).val[j.val]'(by rw [(X a i).property]; exact j.isLt) := by
  have h := getElem_blocks
    (fun a => (⟨blocks (X a), length_blocks (X a)⟩ : Word α (m * B)))
    a (⟨i.val * B + j.val, block_index_lt i j⟩ : Fin (m * B))
  exact h.trans (getElem_blocks (X a) i j)

lemma row_quotient_decomposition (m B p : ℕ) :
    p / B / m * (m * B) + (p / B % m * B + p % B) = p := by
  calc
    p / B / m * (m * B) + (p / B % m * B + p % B) =
        (m * (p / B / m) + p / B % m) * B + p % B := by ring
    _ = p / B * B + p % B := by rw [Nat.div_add_mod]
    _ = p := by simpa only [Nat.mul_comm] using Nat.div_add_mod p B

/-- Quotient/remainder form matching the numerical tagged-row geometric lemmas. -/
lemma getElem_rows_quotient {T m B : ℕ} (X : Fin T → Fin m → Word α B)
    (hm : 0 < m) (hB : 0 < B) (p : ℕ) (hp : p < T * m * B) :
    (rows X)[p]'(by rw [length_rows]; exact hp) =
      (X ⟨p / B / m, row_quotient_lt hm hB hp⟩
         ⟨p / B % m, Nat.mod_lt _ hm⟩).val[p % B]'
        (by rw [(X _ _).property]; exact Nat.mod_lt _ hB) := by
  have h := getElem_rows X
    ⟨p / B / m, row_quotient_lt hm hB hp⟩
    ⟨p / B % m, Nat.mod_lt _ hm⟩ ⟨p % B, Nat.mod_lt _ hB⟩
  simpa only [row_quotient_decomposition] using h

/-- Pairwise-disjoint letter tags force equal matched positions to have the same block index.
The assumption is only cross-family disjointness; no row-boundary alignment is assumed. -/
lemma equal_symbols_same_tag {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (hm : 0 < m) (hB : 0 < B)
    (hdisjoint : ∀ (a b : Fin T) (i j : Fin m) (s : α),
      s ∈ (X a i).val → s ∈ (Y b j).val → i = j)
    (p q : ℕ) (hp : p < T * m * B) (hq : q < T * m * B)
    (heq : (rows X)[p]'(by rw [length_rows]; exact hp) =
      (rows Y)[q]'(by rw [length_rows]; exact hq)) :
    p / B % m = q / B % m := by
  rw [getElem_rows_quotient X hm hB p hp,
      getElem_rows_quotient Y hm hB q hq] at heq
  have hleft := List.getElem_mem
    (l := (X ⟨p / B / m, row_quotient_lt hm hB hp⟩
      ⟨p / B % m, Nat.mod_lt _ hm⟩).val)
    (n := p % B) (by rw [(X _ _).property]; exact Nat.mod_lt _ hB)
  have hright := List.getElem_mem
    (l := (Y ⟨q / B / m, row_quotient_lt hm hB hq⟩
      ⟨q / B % m, Nat.mod_lt _ hm⟩).val)
    (n := q % B) (by rw [(Y _ _).property]; exact Nat.mod_lt _ hB)
  rw [← heq] at hright
  exact congrArg Fin.val (hdisjoint _ _ _ _ _ hleft hright)

end TaggedExtraction
end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedExtraction


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedExtraction.equal_symbols_same_tag.{u} := @_root_.OAI.TreeEdit.BinaryLower.TaggedExtraction.equal_symbols_same_tag.{u}
