-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.common_sublist_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:40:25.924111+00:00
-- url     : https://prove2.me/submissions/30186141-0a8c-49af-b3bc-e964064672eb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/LCSCore.lean:L12-L44
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.common_sublist_lower_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.LCSCore ----
namespace OAI

/-!
Supporting common-subsequence facts for the edit-distance preliminaries.
These lemmas concern ordinary ordered sublists, not contiguous substrings.
-/
namespace TreeEdit.BinaryLower

/-- Two sublists of one word have a common sublist whose deficit is at most
    the sum of their deficits in that word. -/
theorem common_sublist_lower_bound {α : Type*} {u v w : List α}
    (hu : u.Sublist w) (hv : v.Sublist w) :
    ∃ z : List α, z.Sublist u ∧ z.Sublist v ∧
      u.length + v.length ≤ w.length + z.length := by
  induction w generalizing u v with
  | nil =>
      have hu' : u = [] := List.sublist_nil.mp hu
      have hv' : v = [] := List.sublist_nil.mp hv
      subst u
      subst v
      exact ⟨[], .refl _, .refl _, le_rfl⟩
  | cons a w ih =>
      rcases List.sublist_cons_iff.mp hu with huSkip | ⟨u', rfl, huTail⟩
      · rcases List.sublist_cons_iff.mp hv with hvSkip | ⟨v', rfl, hvTail⟩
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huSkip hvSkip
          refine ⟨z, hzu, hzv, ?_⟩
          simp only [List.length_cons]
          omega
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huSkip hvTail
          refine ⟨z, hzu, hzv.cons a, ?_⟩
          simp only [List.length_cons]
          omega
      · rcases List.sublist_cons_iff.mp hv with hvSkip | ⟨v', rfl, hvTail⟩
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huTail hvSkip
          refine ⟨z, hzu.cons a, hzv, ?_⟩
          simp only [List.length_cons]
          omega
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huTail hvTail
          refine ⟨a :: z, hzu.cons_cons a, hzv.cons_cons a, ?_⟩
          simp only [List.length_cons]
          omega

end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.common_sublist_lower_bound := @_root_.OAI.TreeEdit.BinaryLower.common_sublist_lower_bound
