-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteActivity.dense_of_no_sparse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:18:21.161555+00:00
-- url     : https://prove2.me/submissions/c3949c31-199c-4d27-96c1-e95ea15e0b95

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteActivityBridge.lean:L29-L47
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteActivity.dense_of_no_sparse. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Branching_activeLeafCount_eq_card
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Branching_pow_le_activeLeafCount

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

/-- A level-bounded local branching assumption supplies exactly the finite
recursive condition, with no assertion below the terminal level. -/
theorem branchesAtLeast_of_local (A : List α → Prop) (k H h : ℕ)
    (hlocal : ∀ v : List α, v.length < H → A v → k ≤ activeChildCount A v)
    (v : List α) (hv : v.length + h ≤ H) : BranchesAtLeast A k v h := by
  induction h generalizing v with
  | zero => trivial
  | succ h ih =>
    constructor
    · exact hlocal v (by omega)
    · intro i
      apply ih (v ++ [i])
      simp only [List.length_append, List.length_singleton]
      omega

/-- Explicit cardinality form of the active branching bound. -/
theorem pow_le_card_active_paths (A : List α → Prop) [DecidablePred A] (k h : ℕ)
    (v : List α) (hbranch : BranchesAtLeast A k v h) (hv : A v) :
    k ^ h ≤
      (Finset.univ.filter fun f : Fin h → α => A (v ++ List.ofFn f)).card := by
  classical
  rw [← activeLeafCount_eq_card]
  exact pow_le_activeLeafCount A k h v hbranch hv

end TreeEdit.BinaryLower.Branching

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteActivityBridge ----
namespace OAI

/-!
# Finite indices for the sparse-activity obstruction

Internal nodes are indexed by their depth and finite sequence of child
indices. Absence of a sparse active node bounds the cardinality of active
leaves, which controls the Fourier mass.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical

/-- Absence of bad nodes in the finite node indexing gives the full active
leaf cardinality lower bound. -/
theorem dense_of_no_sparse {α : Type*} [Fintype α]
    (active : List α → Prop) (b h : ℕ)
    (hroot : active []) (hno : ¬ ∃ v : InternalNode α h, sparseNode active b v) :
    b ^ h ≤ (Finset.univ.filter fun f : Fin h → α => active (List.ofFn f)).card := by
  classical
  have hlocal : ∀ p : List α, p.length < h → active p →
      b ≤ Branching.activeChildCount active p := by
    intro p hp ha
    by_contra hb
    have hsmall : Branching.activeChildCount active p < b := Nat.lt_of_not_ge hb
    let v : InternalNode α h := ⟨⟨p.length, hp⟩, p.get⟩
    apply hno
    refine ⟨v, ?_⟩
    simpa [sparseNode, v] using And.intro ha hsmall
  have hbranch := Branching.branchesAtLeast_of_local active b h h hlocal [] (by simp)
  simpa only [List.nil_append] using
    Branching.pow_le_card_active_paths active b h [] hbranch hroot

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.dense_of_no_sparse := @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.dense_of_no_sparse
