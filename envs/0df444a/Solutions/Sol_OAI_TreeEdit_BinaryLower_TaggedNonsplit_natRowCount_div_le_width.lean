-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedNonsplit.natRowCount_div_le_width
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:34:42.06321+00:00
-- url     : https://prove2.me/submissions/c7613d60-d15a-495f-a62d-92b44f384831

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean:L197-L218
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedNonsplit.natRowCount_div_le_width. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedNonsplit ----
namespace OAI

/-! Loss counting for nonsplit rows with a local row-pair matching bound. -/

namespace TreeEdit.BinaryLower.TaggedNonsplit

open scoped BigOperators

/-- Capacity of one natural-indexed row under an injective source map. -/
theorem natRowCount_div_le_width {N : ℕ}
    (u : Fin N → ℕ) (hu : Function.Injective u) (W : ℕ) (hW : 0 < W) (r : ℕ) :
    natRowCount (fun i => u i / W) r ≤ W := by
  classical
  unfold natRowCount
  calc
    (Finset.univ.filter fun i => u i / W = r).card ≤ (Finset.range W).card := by
      apply Finset.card_le_card_of_injOn (fun i => u i % W)
      · intro i _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hW)
      · intro i hi j hj hmod
        have hir : u i / W = r := (Finset.mem_filter.mp hi).2
        have hjr : u j / W = r := (Finset.mem_filter.mp hj).2
        apply hu
        have hi' := Nat.mod_add_div (u i) W
        have hj' := Nat.mod_add_div (u j) W
        change u i % W = u j % W at hmod
        rw [hir, hmod] at hi'
        rw [hjr] at hj'
        omega
    _ = W := Finset.card_range W

end TreeEdit.BinaryLower.TaggedNonsplit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedNonsplit
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedNonsplit.natRowCount_div_le_width := @_root_.OAI.TreeEdit.BinaryLower.TaggedNonsplit.natRowCount_div_le_width
