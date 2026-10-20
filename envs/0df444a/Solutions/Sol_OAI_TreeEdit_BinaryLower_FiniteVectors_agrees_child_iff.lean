-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteVectors.agrees_child_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:02:34.416032+00:00
-- url     : https://prove2.me/submissions/b8274dc5-c06b-4895-9586-7f8f10f647ae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean:L114-L130
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteVectors.agrees_child_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteVectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Concrete vectors for the finite tree (finite-tree.tex, finite-vectors).
A prefix is represented by its depth and any full leaf path extending it.
All definitions ignore the unused tail of that representative. No primality
assumption is needed for the annihilation and recursive vector identities. -/

namespace TreeEdit.BinaryLower.FiniteVectors

open scoped BigOperators

variable {m k : ℕ}

lemma agrees_child_iff (j : ℕ) (hj : j < k) (a b : Leaf m k) (i : Fin m) :
    Agrees (j + 1) (Function.update a ⟨j, hj⟩ i) b ↔
      Agrees j a b ∧ b ⟨j, hj⟩ = i := by
  constructor
  · intro h
    constructor
    · intro q hq
      have hne : q ≠ ⟨j, hj⟩ := by intro he; subst q; simp at hq
      simpa only [Function.update_of_ne hne] using h q (by omega)
    · simpa using h ⟨j, hj⟩ (Nat.lt_succ_self j)
  · rintro ⟨h, hi⟩ q hq
    by_cases he : q = ⟨j, hj⟩
    · subst q
      simpa using hi
    · have hval : q.val ≠ j := by intro hv; exact he (Fin.ext hv)
      rw [Function.update_of_ne he]
      exact h q (by omega)

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.agrees_child_iff := @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.agrees_child_iff
