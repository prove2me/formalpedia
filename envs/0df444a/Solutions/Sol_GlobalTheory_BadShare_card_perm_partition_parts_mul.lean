-- Prove2me | solution 1 for GlobalTheory.BadShare.card_perm_partition_parts_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:05:03.899949+00:00
-- url     : https://prove2.me/submissions/bbecc71a-85a5-4638-821a-18cdbeca9eff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermPartitionPartsMulCentralizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare
private lemma eq_filter_add_replicate (μ : Multiset ℕ) (h : ∀ d ∈ μ, 0 < d) :
    μ = μ.filter (fun n => 2 ≤ n) + Multiset.replicate (μ.count 1) 1 := by
  ext d
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases h2 : 2 ≤ d
  · rw [if_pos h2, if_neg (by omega)]; rfl
  · rw [if_neg h2]
    by_cases h1 : 1 = d
    · subst h1; simp
    · rw [if_neg h1]
      have : d ∉ μ := fun hd => by have := h d hd; omega
      simpa using this
end GlobalTheory.BadShare
end

set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution :
    ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N →
      (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card *
        ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  intro N μ hpos hsum
  set m := μ.filter (fun n => 2 ≤ n) with hm
  have hμ : μ = m + Multiset.replicate (μ.count 1) 1 := eq_filter_add_replicate μ hpos
  have hs : m.sum + μ.count 1 = N := by
    rw [← hsum]
    conv_rhs => rw [hμ]
    simp
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin N) m
  rw [if_pos ⟨by rw [Fintype.card_fin]; omega, fun a ha => (Multiset.mem_filter.1 ha).2⟩,
    Fintype.card_fin] at key
  have hN : N - m.sum = μ.count 1 := by omega
  rw [hN] at key
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ) =
      Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.cycleType = m := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, h]
    · intro h
      rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, h, Fintype.card_fin, hN]
      exact hμ.symm
  have hprod : ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) =
      (μ.count 1).factorial * m.prod * ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [← Finset.prod_filter_mul_prod_filter_not μ.toFinset (fun n => 2 ≤ n)]
    have h1 : μ.toFinset.filter (fun n => 2 ≤ n) = m.toFinset := by
      ext n; simp [hm]
    have h2 : ∏ d ∈ μ.toFinset.filter (fun n => ¬ 2 ≤ n),
        (d ^ μ.count d * (μ.count d).factorial) = (μ.count 1).factorial := by
      rw [Finset.prod_eq_single 1]
      · simp
      · intro b hb hb1
        simp only [Finset.mem_filter, Multiset.mem_toFinset] at hb
        have := hpos b hb.1
        omega
      · intro h
        have : (1 : ℕ) ∉ μ := fun h1 => h (by simpa using h1)
        simp [Multiset.count_eq_zero_of_notMem this]
    rw [h1, h2, Finset.prod_multiset_count m, mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hn)).2
    have : m.count n = μ.count n := by rw [hm, Multiset.count_filter, if_pos hn2]
    rw [this]
  rw [hset, hprod]
  convert key
end GlobalTheory.BadShare
