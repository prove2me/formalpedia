-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_many_nondividing_children
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:13:53.765543+00:00
-- url     : https://prove2.me/submissions/c372c56f-550e-4b06-91c2-c56d87efc621

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSeparation.lean:L73-L109
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_many_nondividing_children. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSeparation_card_filter_dvd_lt

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSeparation ----
namespace OAI

/-!
# Large-prime divisor counting

The prime-divisor counting estimate gives the arithmetic step in the
finite-tree separation induction, `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.PrimeSeparation

open scoped BigOperators

/-- Integer form of `card_filter_dvd_lt`, with no sign restriction. -/
theorem card_filter_int_dvd_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (L q : ℕ) (z : ℤ)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hL : ∀ i ∈ s, L ≤ p i)
    (hLpos : 0 < L) (hz : z ≠ 0) (hsmall : z.natAbs < L ^ q) :
    (s.filter fun i => (p i : ℤ) ∣ z).card < q := by
  simpa only [Int.natCast_dvd] using
    card_filter_dvd_lt s p L q z.natAbs hp hinj hL hLpos
      (Int.natAbs_pos.mpr hz) hsmall

/-- The numerical divisor estimate used for two different rows of the finite
construction (`T = k^(20*k)`, primes at least `k^4`). -/
theorem finite_tree_few_prime_divisors {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (k : ℕ) (z : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hlarge : ∀ i ∈ s, k ^ 4 ≤ p i)
    (hz : z ≠ 0) (hsmall : z.natAbs < k ^ (20 * k)) :
    (s.filter fun i => (p i : ℤ) ∣ z).card < 10 * k := by
  apply card_filter_int_dvd_lt s p (k ^ 4) (10 * k) z hp hinj hlarge
  · positivity
  · exact hz
  · apply hsmall.trans_le
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    omega

/-- At least half of the children have periods not dividing the relative
shift between different rows. `Q` is arbitrary here; the product `R` forces
each child prime to divide the distinguished-shift contribution. -/
theorem finite_tree_many_nondividing_children
    (k Q : ℕ) (p : Fin (20 * k) → ℕ) (z t : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ i, k ^ 4 ≤ p i)
    (hz : z ≠ 0) (hsmall : z.natAbs < k ^ (20 * k)) :
    10 * k ≤ (Finset.univ.filter fun i =>
      ¬ ((Q * p i : ℕ) : ℤ) ∣ z + t * (∏ j, p j : ℕ)).card := by
  classical
  let R : ℕ := ∏ j, p j
  have hfew : (Finset.univ.filter fun i => (p i : ℤ) ∣ z).card < 10 * k :=
    finite_tree_few_prime_divisors Finset.univ p k z hk (fun i _ => hp i)
      (fun i _ j _ h => hinj h) (fun i _ => hlarge i) hz hsmall
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (20 * k)))) (fun i => (p i : ℤ) ∣ z)
  have hmany : 10 * k ≤ (Finset.univ.filter fun i => ¬ (p i : ℤ) ∣ z).card := by
    simp only [Finset.card_univ, Fintype.card_fin] at hpartition
    omega
  apply hmany.trans
  apply Finset.card_le_card
  intro i hi
  obtain ⟨_, hnot⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hperiod
  have hprimePeriod : (p i : ℤ) ∣ ((Q * p i : ℕ) : ℤ) := by
    refine ⟨(Q : ℤ), ?_⟩
    push_cast
    ring
  have hprimeR : (p i : ℤ) ∣ (R : ℤ) := by
    exact_mod_cast (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
  have hprimeTerm : (p i : ℤ) ∣ t * (R : ℤ) := dvd_mul_of_dvd_right hprimeR t
  have hprimeSum : (p i : ℤ) ∣ z + t * (R : ℤ) := hprimePeriod.trans hperiod
  apply hnot
  simpa only [add_sub_cancel_right] using dvd_sub hprimeSum hprimeTerm

end TreeEdit.BinaryLower.PrimeSeparation

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSeparation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_many_nondividing_children := @_root_.OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_many_nondividing_children
