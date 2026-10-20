-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_child
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:03:52.831032+00:00
-- url     : https://prove2.me/submissions/ddb2c189-7876-4e5f-b900-cc0ddcfcd128

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean:L190-L216
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_child. The node keeps its source
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

lemma prefixPeriod_child (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) (i : Fin m) :
    prefixPeriod p (j + 1) (Function.update a ⟨j, hj⟩ i) =
      prefixPeriod p j a * p ⟨j, hj⟩ i := by
  have hs : Finset.univ.filter (fun q : Fin k => q.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun q : Fin k => q.val < j)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hq
      by_cases he : q.val = j
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | hq)
      · exact Nat.lt_succ_self j
      · omega
  have hn : (⟨j, hj⟩ : Fin k) ∉ Finset.univ.filter (fun q : Fin k => q.val < j) := by simp
  have hp : (∏ q ∈ Finset.univ.filter (fun q : Fin k => q.val < j),
      p q (Function.update a ⟨j, hj⟩ i q)) =
      ∏ q ∈ Finset.univ.filter (fun q : Fin k => q.val < j), p q (a q) := by
    apply Finset.prod_congr rfl
    intro q hq
    have hlt := (Finset.mem_filter.mp hq).2
    have he : q ≠ ⟨j, hj⟩ := by intro he; subst q; simp at hlt
    rw [Function.update_of_ne he]
  simp only [prefixPeriod, hs, Finset.prod_insert hn, Function.update_self, hp]
  ring

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_child := @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_child
