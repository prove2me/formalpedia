-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_leaf_script
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:48:32.975595+00:00
-- url     : https://prove2.me/submissions/04687d2f-a61e-4d1b-bc3b-ffe31ee4c7c2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeCosts.lean:L127-L150
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_leaf_script. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_descendant_script

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeCosts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Inexpensive scripts in the recursive row evaluator

Local row advancement and descendant-occurrence lifting establish
`lem:finite-cost` from geometric hypotheses on state translations and
invisible leaf decoders.
-/

namespace TreeEdit.BinaryLower.FiniteTree

open CheapTranslations

variable {A Γ : Type*} [AddCommMonoid A]

/-- Changing only one leaf decoder costs one substitution in each of its
`T^q.length` occurrences, irrespective of how much its state changes. -/
theorem nodeWord_leaf_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (q p : List (Fin m)) (z : A)
    (houtside : ∀ r : List (Fin m), r.length = q.length → r ≠ q →
      ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u q.length p x)
      (nodeWord T leaf u q.length p (x + z)) (T ^ q.length) := by
  have hlocal : ∀ y, EditScript (nodeWord T leaf u 0 (p ++ q) y)
      (nodeWord T leaf u 0 (p ++ q) (y + z)) 1 := by
    intro y
    exact EditScript.cons
      (EditStep.substitute [] [] (leaf (p ++ q) y) (leaf (p ++ q) (y + z)))
      (EditScript.nil _)
  have hout : ∀ r : List (Fin m), r.length = 0 + q.length →
      ¬ q.IsPrefix r → ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y := by
    intro r hr hn y
    apply houtside r (by simpa using hr) _ y
    intro heq
    subst r
    exact hn List.prefix_rfl
  simpa using nodeWord_descendant_script T leaf u 0 q p z 1 hlocal hout x

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open CheapTranslations


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_leaf_script := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_leaf_script
