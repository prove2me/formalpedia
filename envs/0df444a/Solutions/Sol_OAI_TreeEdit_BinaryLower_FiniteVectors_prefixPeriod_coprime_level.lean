-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_coprime_level
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:08:08.858992+00:00
-- url     : https://prove2.me/submissions/c80eb1f3-31a5-48c0-861c-19fa4b81be61

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean:L273-L296
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_coprime_level. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_prefixPeriod_eq_prod_cast

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

/-- Distinct odd depth/child primes make the prefix period coprime to the
current level. This is a specialization to the concrete vector API of the
prime-product coprimality calculation in `lem:orders`. -/
lemma prefixPeriod_coprime_level (p : Fin k → Fin m → ℕ)
    (hinj : Function.Injective (fun z : Fin k × Fin m => p z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (p q i)) (hodd : ∀ q i, p q i ≠ 2)
    (j : ℕ) (hj : j < k) (a : Leaf m k) :
    Nat.Coprime (prefixPeriod p j a) (levelProduct p ⟨j, hj⟩) := by
  rw [prefixPeriod_eq_prod_cast p j hj.le a]
  unfold levelProduct
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.prod_right
    intro i hi
    exact (Nat.coprime_primes Nat.prime_two (hprime _ i)).mpr (Ne.symm (hodd _ i))
  · apply Nat.Coprime.prod_left
    intro q hq
    apply Nat.Coprime.prod_right
    intro i hi
    apply (Nat.coprime_primes (hprime _ _) (hprime _ _)).mpr
    intro he
    have hpair := @hinj (Fin.castLE hj.le q, a (Fin.castLE hj.le q)) (⟨j, hj⟩, i) he
    have hval := congrArg (fun z : Fin k × Fin m => z.1.val) hpair
    simp only [Fin.val_castLE] at hval
    exact (Nat.ne_of_lt q.isLt) hval

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_coprime_level := @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_coprime_level
