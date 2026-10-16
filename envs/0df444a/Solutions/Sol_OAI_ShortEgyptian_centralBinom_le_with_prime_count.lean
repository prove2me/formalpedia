-- Prove2me | solution 1 for OAI.ShortEgyptian.centralBinom_le_with_prime_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:30:48.218949+00:00
-- url     : https://prove2.me/submissions/0d84fd55-0928-43a7-ac76-602e98adca06

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeLists.lean:L10-L72
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.centralBinom_le_with_prime_count. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeLists ----
namespace OAI

namespace ShortEgyptian

open Finset
theorem centralBinom_le_with_prime_count (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3)*(2*n)^(dyadicPrimes n).card := by
  classical
  let f p := p ^ n.centralBinom.factorization p
  let A := Nat.primesLE (2*n/3)
  let B := dyadicPrimes n
  have hpos : 0 < n := by omega
  have htwo : 1 ≤ 2*n := by omega
  have hdis : Disjoint A B := by
    rw [disjoint_left]
    intro p hpA hpB
    have hpa := (Nat.mem_primesLE.mp hpA).1
    have hpb := (mem_Ioc.mp (mem_filter.mp hpB).1).1
    have : 2*n/3 ≤ n := by omega
    omega
  have hab : n.centralBinom = (∏ p ∈ A, f p)*(∏ p ∈ B, f p) := by
    rw [← prod_union hdis]
    rw [← n.prod_pow_factorization_centralBinom]
    symm
    apply prod_subset
    · intro p hp
      rcases mem_union.mp hp with hp | hp
      · have hh := (Nat.mem_primesLE.mp hp).1
        exact mem_range.mpr (by omega)
      · exact mem_range.mpr (by have hh := (mem_Ioc.mp (mem_filter.mp hp).1).2; omega)
    · intro p hp hpnot
      dsimp [f]
      by_cases hprime : p.Prime
      · have hplow : 2*n/3 < p := by
          by_contra! h
          exact hpnot (mem_union.mpr (Or.inl (Nat.mem_primesLE.mpr ⟨h,hprime⟩)))
        have hpn : p ≤ n := by
          by_contra! h
          exact hpnot (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h,by have hh := mem_range.mp hp; omega⟩,hprime⟩)))
        have hthree : 2*n < 3*p := by omega
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hthree,pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hprime,pow_zero]
  have hlow : (∏ p ∈ A, f p) ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3) := by
    rw [← prod_filter_mul_prod_filter_not A (fun p => p ≤ Nat.sqrt (2*n))]
    apply mul_le_mul'
    · apply (prod_le_prod' (fun p _ => (show f p ≤ 2*n from Nat.pow_factorization_choose_le (by omega)))).trans
      rw [prod_const]
      apply Nat.pow_le_pow_right htwo
      apply (card_le_card (show A.filter (fun p => p ≤ Nat.sqrt (2*n)) ⊆ Icc 1 (Nat.sqrt (2*n)) from ?_)).trans
      · rw [Nat.card_Icc,Nat.add_sub_cancel]
      · intro p hp
        exact mem_Icc.mpr ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.one_lt.le,(mem_filter.mp hp).2⟩
    · apply le_trans _ (primorial_le_four_pow (2*n/3))
      have hp : ∀ p ∈ A.filter (fun p => ¬p ≤ Nat.sqrt (2*n)), f p ≤ p := by
        intro p hp
        have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        have hlarge := (mem_filter.mp hp).2
        have hf : n.centralBinom.factorization p ≤ 1 := Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hlarge))
        exact (Nat.pow_le_pow_right hprime.one_lt.le hf).trans_eq (pow_one p)
      apply (prod_le_prod' hp).trans
      change (∏ p ∈ A.filter (fun p => ¬p ≤ Nat.sqrt (2*n)), p) ≤ ∏ p ∈ A, p
      exact prod_le_prod_of_subset_of_one_le' (filter_subset _ _) (fun p hp _ => (Nat.mem_primesLE.mp hp).2.one_lt.le)
  have hhigh : (∏ p ∈ B, f p) ≤ (2*n)^B.card := by
    calc
      _ ≤ ∏ _p ∈ B, 2*n := prod_le_prod' (fun p _ => Nat.pow_factorization_choose_le (by omega))
      _ = _ := prod_const _
  rw [hab]
  exact mul_le_mul' hlow hhigh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.centralBinom_le_with_prime_count := @_root_.OAI.ShortEgyptian.centralBinom_le_with_prime_count
