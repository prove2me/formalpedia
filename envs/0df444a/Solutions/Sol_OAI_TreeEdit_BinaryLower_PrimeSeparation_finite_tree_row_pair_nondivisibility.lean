-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_row_pair_nondivisibility
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:15:20.612991+00:00
-- url     : https://prove2.me/submissions/55bdf0be-5e36-49ed-b560-f8d36011e2a9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSeparation.lean:L123-L147
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_row_pair_nondivisibility. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSeparation_finite_tree_many_nondividing_children

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSeparation ----
namespace OAI

/-!
# Large-prime divisor counting

The prime-divisor counting estimate gives the arithmetic step in the
finite-tree separation induction, `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.PrimeSeparation

open scoped BigOperators

/-- For the same row on both sides, coprimality of the parent period and
`R` prevents every child period from dividing the distinguished shift. -/
theorem not_child_period_dvd_mul (Q R p : ℕ) (t : ℤ)
    (hcop : Nat.Coprime Q R) (ht : ¬ (Q : ℤ) ∣ t) :
    ¬ ((Q * p : ℕ) : ℤ) ∣ t * (R : ℤ) := by
  intro h
  have hparent : (Q : ℤ) ∣ ((Q * p : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_right Q p)
  have hn : Q ∣ (t * (R : ℤ)).natAbs := Int.natCast_dvd.mp (hparent.trans h)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hn
  exact ht (Int.natCast_dvd.mpr (hcop.dvd_mul_right.mp hn))

/-- Complete row-pair arithmetic in Proposition `prop:finite-separation`.
Every pair of legal row indices has at least `m/2 = 10*k` children for which
the relative shift is nonzero modulo the child period. -/
theorem finite_tree_row_pair_nondivisibility
    (k Q : ℕ) (p : Fin (20 * k) → ℕ) (a b : ℕ) (t : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ i, k ^ 4 ≤ p i)
    (ha : a < k ^ (20 * k)) (hb : b < k ^ (20 * k))
    (hcop : Nat.Coprime Q (∏ j, p j)) (ht : ¬ (Q : ℤ) ∣ t) :
    10 * k ≤ (Finset.univ.filter fun i =>
      ¬ ((Q * p i : ℕ) : ℤ) ∣
        (b : ℤ) - a + t * (∏ j, p j : ℕ)).card := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [sub_self, zero_add]
    have hall : ∀ i : Fin (20 * k),
        ¬ ((Q * p i : ℕ) : ℤ) ∣ t * (∏ j, p j : ℕ) := fun i =>
      not_child_period_dvd_mul Q (∏ j, p j) (p i) t hcop ht
    simpa only [hall, not_false_eq_true, Finset.filter_true, Finset.card_univ,
      Fintype.card_fin] using (show 10 * k ≤ 20 * k by omega)
  · apply finite_tree_many_nondividing_children k Q p ((b : ℤ) - a) t
      hk hp hinj hlarge
    · omega
    · omega

end TreeEdit.BinaryLower.PrimeSeparation

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSeparation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_row_pair_nondivisibility := @_root_.OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_row_pair_nondivisibility
