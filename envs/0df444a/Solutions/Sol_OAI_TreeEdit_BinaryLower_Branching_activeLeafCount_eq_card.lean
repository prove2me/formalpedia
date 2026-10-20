-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Branching.activeLeafCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:16:38.603298+00:00
-- url     : https://prove2.me/submissions/3acd871c-a59b-4cb7-95a9-37f0180a013d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Branching.lean:L75-L102
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Branching.activeLeafCount_eq_card. The node keeps its source
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

/-- The recursive count is the ordinary finite cardinality of active
paths of length `h`, represented by functions on `Fin h`. -/
theorem activeLeafCount_eq_card (A : List α → Prop) [DecidablePred A] (v : List α) (h : ℕ) :
    activeLeafCount A v h =
      (Finset.univ.filter fun f : Fin h → α => A (v ++ List.ofFn f)).card := by
  classical
  induction h generalizing v with
  | zero =>
    by_cases hv : A v <;> simp [activeLeafCount, hv]
  | succ h ih =>
    rw [activeLeafCount, Finset.card_filter]
    calc
      (∑ i : α, activeLeafCount A (v ++ [i]) h) =
          ∑ i : α, ∑ f : Fin h → α,
            if A ((v ++ [i]) ++ List.ofFn f) then 1 else 0 := by
              simp only [ih, Finset.card_filter]
      _ = ∑ z : α × (Fin h → α),
            if A ((v ++ [z.1]) ++ List.ofFn z.2) then 1 else 0 :=
        (Fintype.sum_prod_type (fun z : α × (Fin h → α) =>
          if A ((v ++ [z.1]) ++ List.ofFn z.2) then (1 : ℕ) else 0)).symm
      _ = ∑ f : Fin (h + 1) → α,
            if A (v ++ List.ofFn f) then 1 else 0 := by
        apply Fintype.sum_equiv (Fin.consEquiv fun _ => α)
        intro z
        change (if A ((v ++ [z.1]) ++ List.ofFn z.2) then 1 else 0) =
          (if A (v ++ List.ofFn (Fin.cons z.1 z.2)) then 1 else 0)
        rw [List.ofFn_cons]
        simp only [List.append_assoc, List.singleton_append]

end TreeEdit.BinaryLower.Branching

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Branching


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Branching.activeLeafCount_eq_card := @_root_.OAI.TreeEdit.BinaryLower.Branching.activeLeafCount_eq_card
