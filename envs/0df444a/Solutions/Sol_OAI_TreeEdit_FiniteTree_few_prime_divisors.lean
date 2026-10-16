-- Prove2me | solution 1 for OAI.TreeEdit.FiniteTree.few_prime_divisors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:45:23.540305+00:00
-- url     : https://prove2.me/submissions/5df3e5d4-55c4-464a-a0df-7d2aed16d020

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/TreeArithmetic.lean:L20-L40
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteTree.few_prime_divisors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic

-- ---- from OAI.Combinatorics.TreeEdit.TreeArithmetic ----
namespace OAI

namespace TreeEdit.FiniteTree

universe u

attribute [local instance] Classical.propDecidable

lemma few_prime_divisors {m b s T : ℕ} (p : Fin m → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hb : 1 ≤ b) (hpb : ∀ i, b ≤ p i) (hT : T ≤ b ^ s)
    (d : ℤ) (hd : d ≠ 0) (hdT : d.natAbs < T) :
    (Finset.univ.filter (fun i => (p i : ℤ) ∣ d)).card < s := by
  classical
  let S := Finset.univ.filter (fun i => (p i : ℤ) ∣ d)
  have hcop : (↑S : Set (Fin m)).Pairwise (fun i j => IsCoprime (p i : ℤ) (p j : ℤ)) := by
    intro i _ j _ hij
    exact ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))).isCoprime
  have hprod : (∏ i ∈ S, (p i : ℤ)) ∣ d :=
    Finset.prod_dvd_of_coprime hcop (fun i hi => (Finset.mem_filter.mp hi).2)
  have hprod' : (∏ i ∈ S, p i) ∣ d.natAbs := Int.natCast_dvd.mp (by simpa using hprod)
  have hle : b ^ S.card ≤ d.natAbs := by
    calc
      _ = ∏ _i ∈ S, b := (Finset.prod_const b).symm
      _ ≤ ∏ i ∈ S, p i := Finset.prod_le_prod' (fun i _ => hpb i)
      _ ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hprod'
  by_contra hn
  have hh := pow_le_pow_right₀ hb (Nat.le_of_not_gt hn)
  exact (not_le_of_gt hdT) (hT.trans (hh.trans hle))

end TreeEdit.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteTree
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteTree.few_prime_divisors := @_root_.OAI.TreeEdit.FiniteTree.few_prime_divisors
