-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.symbol_prefix_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:19:52.323087+00:00
-- url     : https://prove2.me/submissions/f0b54dd8-95ae-4e41-a335-88bbac8ba0f2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeTags.lean:L15-L34
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.symbol_prefix_of_mem. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeTags ----
namespace OAI

/-!
# Concrete tagged alphabets below finite-tree nodes

The generic row lemma needs disjoint alphabets for distinct children. Here
that hypothesis is proved for the actual tagged cyclic-state symbols, not
postulated as an additional property of the construction.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- Every symbol in a genuine subtree word retains a leaf extending its prefix. -/
theorem symbol_prefix_of_mem {m k T : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State Q) (s : Symbol Q)
    (hs : s ∈ nodeWord T (leafDecoder Q base) u h p x) : p <+: s.1.val := by
  induction h generalizing p x with
  | zero =>
      have hp : p.length = k := by simpa using hlen
      simp only [nodeWord, List.mem_singleton] at hs
      subst s
      rw [leafDecoder_of_length Q base p hp x]
  | succ h ih =>
      simp only [nodeWord, List.mem_flatMap] at hs
      obtain ⟨a, ha, i, hi, hmem⟩ := hs
      have hlenChild : (p ++ [i]).length + h = k := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hchild := ih (p ++ [i]) hlenChild (x + a • u p) hmem
      exact (List.prefix_append p [i]).trans hchild

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.symbol_prefix_of_mem := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.symbol_prefix_of_mem
