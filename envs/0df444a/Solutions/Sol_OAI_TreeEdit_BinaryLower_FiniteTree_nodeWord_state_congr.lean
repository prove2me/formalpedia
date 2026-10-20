-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_state_congr
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:55:43.165242+00:00
-- url     : https://prove2.me/submissions/3f8aa139-06e0-42a6-8f23-4b7d9d3d7c4b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeGeometry.lean:L38-L63
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_state_congr. The node keeps its source
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

/-- At a valid leaf, equality is exactly equality of that leaf's state. -/
theorem leafDecoder_eq_iff {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k) (x y : State Q) :
    leafDecoder Q base p x = leafDecoder Q base p y ↔
      x ⟨p, hp⟩ = y ⟨p, hp⟩ := by
  simp [leafDecoder, hp]

/-- The recursive word depends only on the coordinates below its prefix,
even though ancestor shifts may offset all coordinates of the supplied state. -/
theorem nodeWord_state_congr {T m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x y : State Q) (hagree : ∀ l : Leaf m k, p <+: l.val → x l = y l) :
    nodeWord T (leafDecoder Q base) u h p x =
      nodeWord T (leafDecoder Q base) u h p y := by
  induction h generalizing p x y with
  | zero =>
      have hp : p.length = k := by simpa using hlen
      simp only [nodeWord, List.singleton_inj]
      apply (leafDecoder_eq_iff Q base p hp x y).2
      exact hagree ⟨p, hp⟩ (by rfl)
  | succ h ih =>
      simp only [nodeWord]
      apply List.flatMap_congr
      intro a ha
      apply List.flatMap_congr
      intro i hi
      apply ih
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro l hl
        have hp : p <+: l.val := (List.prefix_append p [i]).trans hl
        simp only [Pi.add_apply, hagree l hp]

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_state_congr := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_state_congr
