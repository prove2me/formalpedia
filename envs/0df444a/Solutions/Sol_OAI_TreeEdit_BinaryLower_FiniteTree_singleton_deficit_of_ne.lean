-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.singleton_deficit_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:59:06.76367+00:00
-- url     : https://prove2.me/submissions/b18b179b-0770-42be-9323-4d5a3321d594

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeGeometry.lean:L100-L118
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.singleton_deficit_of_ne. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeGeometry ----
namespace OAI

/-! Concrete tagged leaf states and subtree locality for the finite tree. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- Two different singleton words have unit one-sided deficit. -/
theorem singleton_deficit_of_ne {Γ : Type*} (a b : Γ) (hab : a ≠ b) :
    deficit 1 [a] [b] = 1 := by
  have hset : {n : ℕ | ∃ z : List Γ, z.Sublist [a] ∧ z.Sublist [b] ∧ z.length = n}
      = {0} := by
    ext n
    constructor
    · rintro ⟨z, hza, hzb, rfl⟩
      rcases List.sublist_singleton.1 hza with rfl | rfl
      · simp
      · have : a = b := by simpa using hzb
        exact (hab this).elim
    · intro hn
      have : n = 0 := by simpa using hn
      subst n
      exact ⟨[], by simp⟩
  unfold deficit lcs
  rw [hset]
  simp

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.singleton_deficit_of_ne := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.singleton_deficit_of_ne
