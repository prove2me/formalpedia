-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteVectors.leafPeriod_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:00:57.675333+00:00
-- url     : https://prove2.me/submissions/88bd1ad4-77f9-4304-94a0-5af0b90eacb1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean:L76-L90
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteVectors.leafPeriod_dvd. The node keeps its source
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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Concrete vectors for the finite tree (finite-tree.tex, finite-vectors).
A prefix is represented by its depth and any full leaf path extending it.
All definitions ignore the unused tail of that representative. No primality
assumption is needed for the annihilation and recursive vector identities. -/

namespace TreeEdit.BinaryLower.FiniteVectors

open scoped BigOperators

variable {m k : ℕ}

/-- The full leaf modulus divides its prefix period times the suffix scale. -/
lemma leafPeriod_dvd (p : Fin k → Fin m → ℕ) (j : ℕ) (a b : Leaf m k)
    (hab : Agrees j a b) : leafPeriod p b ∣ prefixPeriod p j a * suffixScale p j := by
  have hprod : (∏ q, p q (b q)) ∣
      ∏ q : Fin k, if q.val < j then p q (a q) else levelProduct p q := by
    apply Finset.prod_dvd_prod_of_dvd
    intro q hq
    by_cases hj : q.val < j
    · simp only [ite_eq_left hj, hab q hj]
      exact dvd_rfl
    · simp only [ite_eq_right hj, levelProduct]
      exact Finset.dvd_prod_of_mem (fun i => p q i) (Finset.mem_univ (b q))
  rw [Finset.prod_ite] at hprod
  have h := Nat.mul_dvd_mul_left 2 hprod
  simpa only [leafPeriod, prefixPeriod, suffixScale, Nat.not_lt, mul_assoc] using h

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.leafPeriod_dvd := @_root_.OAI.TreeEdit.BinaryLower.FiniteVectors.leafPeriod_dvd
