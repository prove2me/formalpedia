-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.PrimeSeparation.card_filter_dvd_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:12:23.306734+00:00
-- url     : https://prove2.me/submissions/4a48dac1-0eb5-4618-98a7-58dcea7ec548

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/PrimeSeparation.lean:L16-L42
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.PrimeSeparation.card_filter_dvd_lt. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.PrimeSeparation ----
namespace OAI

/-!
# Large-prime divisor counting

The prime-divisor counting estimate gives the arithmetic step in the
finite-tree separation induction, `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.PrimeSeparation

open scoped BigOperators

/-- Fewer than `q` distinct primes at least `L` can divide a positive
integer smaller than `L ^ q`. The indexing set need not be all of a type. -/
theorem card_filter_dvd_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (L q n : ℕ)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hL : ∀ i ∈ s, L ≤ p i)
    (hLpos : 0 < L) (hnpos : 0 < n) (hn : n < L ^ q) :
    (s.filter fun i => p i ∣ n).card < q := by
  classical
  let t := s.filter fun i => p i ∣ n
  have hts : ∀ i ∈ t, i ∈ s := fun i hi => (Finset.mem_filter.mp hi).1
  have hprod : (∏ i ∈ t, p i) ∣ n := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i hi j hj hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (Nat.coprime_primes (hp i (hts i hi)) (hp j (hts j hj))).mpr
      exact fun heq => hij (hinj (hts i hi) (hts j hj) heq)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hprodle : (∏ i ∈ t, p i) ≤ n := Nat.le_of_dvd hnpos hprod
  have hlow : L ^ t.card ≤ ∏ i ∈ t, p i :=
    Finset.pow_card_le_prod t p L fun i hi => hL i (hts i hi)
  change t.card < q
  by_contra h
  have hq : q ≤ t.card := Nat.le_of_not_gt h
  exact (not_le_of_gt hn) ((Nat.pow_le_pow_right hLpos hq).trans (hlow.trans hprodle))

end TreeEdit.BinaryLower.PrimeSeparation

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.PrimeSeparation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.PrimeSeparation.card_filter_dvd_lt := @_root_.OAI.TreeEdit.BinaryLower.PrimeSeparation.card_filter_dvd_lt
