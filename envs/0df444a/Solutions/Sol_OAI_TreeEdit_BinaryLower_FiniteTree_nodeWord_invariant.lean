-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:53:47.748438+00:00
-- url     : https://prove2.me/submissions/e7c7284d-b6d7-453b-b619-d4568a243705

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeWords.lean:L56-L79
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_invariant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeWords ----
namespace OAI

/-!
# Recursive row words for the finite tree

The recursion in equation (finite-word) uses an additive state group,
node shifts and leaf symbols. It is instantiated with the product of
cyclic groups in the manuscript.
-/

namespace TreeEdit.BinaryLower.FiniteTree

variable {A Γ : Type*} [AddCommMonoid A]

/-- A translation invisible at every descendant leaf is invisible in the
complete recursive word. The hypothesis is required for all states, permitting
all ancestor offsets without adding any invariance assumption on the shifts. -/
theorem nodeWord_invariant {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (z : A)
    (hinv : ∀ q : List (Fin m), q.length = h → ∀ x : A,
      leaf (p ++ q) (x + z) = leaf (p ++ q) x) (x : A) :
    nodeWord T leaf u h p (x + z) = nodeWord T leaf u h p x := by
  induction h generalizing p x with
  | zero =>
      have hi := hinv [] rfl x
      simpa [nodeWord] using congrArg (fun a => [a]) hi
  | succ h ih =>
      simp only [nodeWord]
      apply List.flatMap_congr
      intro a ha
      apply List.flatMap_congr
      intro i hi
      rw [add_right_comm x z]
      apply ih
      intro q hq y
      have he : ([i] ++ q).length = h + 1 := by simp [hq]
      simpa [List.append_assoc] using hinv ([i] ++ q) he y

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_invariant := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_invariant
