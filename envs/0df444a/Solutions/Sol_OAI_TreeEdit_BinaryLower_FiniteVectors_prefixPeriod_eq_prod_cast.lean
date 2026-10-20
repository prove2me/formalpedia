-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_eq_prod_cast
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:06:50.969962+00:00
-- url     : https://prove2.me/submissions/4f0be7d1-ebb2-4130-b01a-7db999de754c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean:L245-L262
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_eq_prod_cast. The node keeps its source
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

/-- Prefix products agree with the usual dependent `Fin j` path product. -/
lemma prefixPeriod_eq_prod_cast (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j ≤ k)
    (a : Leaf m k) : prefixPeriod p j a =
      2 * ∏ q : Fin j, p (Fin.castLE hj q) (a (Fin.castLE hj q)) := by
  unfold prefixPeriod
  congr 1
  apply Finset.prod_bij (fun q hq => (⟨q.val, (Finset.mem_filter.mp hq).2⟩ : Fin j))
  · intro q hq
    exact Finset.mem_univ _
  · intro q₁ h₁ q₂ h₂ he
    exact Fin.ext (congrArg (fun r : Fin j => r.val) he)
  · intro q hq
    refine ⟨Fin.castLE hj q, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
      exact q.isLt
    · rfl
  · intro q hq
    rfl

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_eq_prod_cast := @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_eq_prod_cast
