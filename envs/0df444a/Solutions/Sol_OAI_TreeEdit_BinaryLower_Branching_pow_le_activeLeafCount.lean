-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Branching.pow_le_activeLeafCount
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:14:59.930622+00:00
-- url     : https://prove2.me/submissions/8cedd696-9f2b-4434-866d-81e26945edb0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Branching.lean:L34-L58
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Branching.pow_le_activeLeafCount. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching

-- ---- from OAI.Combinatorics.BinaryEdit.Branching ----
namespace OAI

/-!
# Counting active leaves in a full ordered tree

A node is its path, a list of child labels. `activeLeafCount A v h`
counts the active descendants exactly `h` edges below `v`. The condition
`BranchesAtLeast A k v h` concerns only internal nodes of that finite
subtree; it makes no assertion about children below its leaves.
-/

namespace TreeEdit.BinaryLower.Branching

variable {α : Type*} [Fintype α]

/-- If every active internal node has at least `k` active children,
then an active root has at least `k ^ h` active leaves at depth `h`.
No branching condition is imposed below depth `h`. -/
theorem pow_le_activeLeafCount (A : List α → Prop) (k h : ℕ)
    (v : List α) (hbranch : BranchesAtLeast A k v h) (hv : A v) :
    k ^ h ≤ activeLeafCount A v h := by
  classical
  induction h generalizing v with
  | zero => simp [activeLeafCount, hv]
  | succ h ih =>
    rcases hbranch with ⟨hroot, hchildren⟩
    let S : Finset α := Finset.univ.filter fun i => A (v ++ [i])
    have hcard : k ≤ S.card := hroot hv
    have hchild : ∀ i ∈ S, k ^ h ≤ activeLeafCount A (v ++ [i]) h := by
      intro i hi
      exact ih (v ++ [i]) (hchildren i) (Finset.mem_filter.mp hi).2
    calc
      k ^ (h + 1) = k ^ h * k := pow_succ k h
      _ ≤ k ^ h * S.card := Nat.mul_le_mul_left _ hcard
      _ = ∑ _i ∈ S, k ^ h := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ S, activeLeafCount A (v ++ [i]) h :=
        Finset.sum_le_sum hchild
      _ ≤ ∑ i : α, activeLeafCount A (v ++ [i]) h :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = activeLeafCount A v (h + 1) := rfl

end TreeEdit.BinaryLower.Branching

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Branching


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Branching.pow_le_activeLeafCount := @_root_.OAI.TreeEdit.BinaryLower.Branching.pow_le_activeLeafCount
