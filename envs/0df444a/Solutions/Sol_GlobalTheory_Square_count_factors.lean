-- Prove2me | solution 1 for GlobalTheory.Square.count_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:12.764594+00:00
-- url     : https://prove2.me/submissions/b61ca092-3a47-4d6e-8225-c029a02af95c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumCompLeSumOfInjOn
import Theorems.Thm_GlobalTheory_Square_sum_le_sum_add_card_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.Square
namespace GlobalTheory.Square
theorem _root_.solution : ∀ (e p q e0 h0 : ℕ), e0 + p = e + q → e0 ≤ h0 → ∀ (v a n0 : ℤ → ℝ) (er : ℝ), 0 ≤ er → (∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q → 0 ≤ a s ∧ 0 ≤ n0 s ∧ v s ≤ a s + er ∧ -(v s) ≤ a s + n0 s) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → v s = v (1 - s)) → (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s) + (∑ k ∈ range p, v ((e : ℤ) + q - k)) - (∑ k ∈ range q, v ((e : ℤ) + k + 1)) ≤ 4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) + ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
  intro e p q e0 h0 he hle v a n0 er her H hsym
  set S : Finset ℤ := Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ) with hS
  have hmem : ∀ s : ℤ, s ∈ S ↔ 1 ≤ s ∧ s ≤ (h0 : ℤ) + p + q := by
    intro s; simp [hS]
  have ha : ∀ s ∈ S, 0 ≤ a s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).1
  have hn : ∀ s ∈ S, 0 ≤ n0 s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).2.1
  have hsplit : ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s
      = ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s + ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s := by
    rw [← Finset.sum_union]
    · congr 1
      ext s
      simp only [mem_union, mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro s h1 h2
      simp only [mem_Icc] at h1 h2
      omega
  have b1 : ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s ≤ ∑ s ∈ S, a s + (e0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 - (e0 : ℤ)) 0) S (fun s => 1 - s) a v er
      (fun x _ y _ h => by simpa using h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        rw [hsym t ht.1 ht.2]
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 - (e0 : ℤ)) 0).card = e0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b2 : ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s ≤ ∑ s ∈ S, a s + (h0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 : ℤ) (h0 : ℤ)) S (fun s => s) a v er
      (fun x _ y _ h => h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 : ℤ) (h0 : ℤ)).card = h0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b3 : ∑ k ∈ range p, v ((e : ℤ) + q - k) ≤ ∑ s ∈ S, a s + (p : ℝ) * er := by
    have := sum_le_sum_add_card_mul (range p) S (fun k : ℕ => (e : ℤ) + q - k) a
      (fun k : ℕ => v ((e : ℤ) + q - k)) er
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) ha
      (fun t ht => by
        simp only [mem_range] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    rwa [card_range] at this
  have b4 : ∑ k ∈ range q, -v ((e : ℤ) + k + 1) ≤ ∑ s ∈ S, (a s + n0 s) + (q : ℝ) * 0 := by
    have := sum_le_sum_add_card_mul (range q) S (fun k : ℕ => (e : ℤ) + k + 1)
      (fun s => a s + n0 s) (fun k : ℕ => -v ((e : ℤ) + k + 1)) 0
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega)
      (fun s hs => add_nonneg (ha s hs) (hn s hs))
      (fun t ht => by
        simp only [mem_range] at ht
        rw [add_zero]
        exact (H _ (by omega) (by omega)).2.2.2)
    rwa [card_range] at this
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at b4
  have hN : 0 ≤ ∑ s ∈ S, n0 s := Finset.sum_nonneg hn
  have hA : 0 ≤ ∑ s ∈ S, a s := Finset.sum_nonneg ha
  have hcount : ((e0 : ℝ) + h0 + p) * er ≤ ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
    refine mul_le_mul_of_nonneg_right ?_ her
    have : e0 + h0 + p ≤ 2 * (h0 + p + q) := by omega
    exact_mod_cast this
  rw [hsplit]
  linarith
end GlobalTheory.Square
