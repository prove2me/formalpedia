-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.extendPrefix_append
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:09:58.536218+00:00
-- url     : https://prove2.me/submissions/6df71137-75b7-4704-a2f5-1d292025d783

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeInstantiation.lean:L43-L59
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.extendPrefix_append. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation ----
namespace OAI

/-! Instantiate the recursive word evaluator with the explicit finite state
group and subtree vectors. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

theorem extendPrefix_append {m k : ℕ} (i₀ i : Fin m) (p : List (Fin m))
    (hp : p.length < k) :
    extendPrefix i₀ (p ++ [i]) = Function.update (extendPrefix i₀ p) ⟨p.length, hp⟩ i := by
  funext q
  by_cases hq : q.val < p.length
  · have hne : q ≠ ⟨p.length, hp⟩ := by intro he; subst q; simp at hq
    simp only [Function.update_of_ne hne, extendPrefix]
    exact List.getD_append p [i] i₀ q.val hq
  · have hq' : p.length ≤ q.val := Nat.le_of_not_gt hq
    by_cases he : q.val = p.length
    · have heq : q = ⟨p.length, hp⟩ := Fin.ext he
      subst q
      simp [extendPrefix, List.getD_eq_getElem?_getD]
    · have hne : q ≠ ⟨p.length, hp⟩ := by intro h; exact he (congrArg Fin.val h)
      simp only [Function.update_of_ne hne, extendPrefix]
      rw [List.getD_eq_default (p ++ [i]) i₀ (by simp; omega)]
      rw [List.getD_eq_default p i₀ hq']

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.extendPrefix_append := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.extendPrefix_append
