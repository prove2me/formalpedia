-- Prove2me | solution 1 for GlobalTheory.prod_eq_sum_of_factorwise_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:52.893041+00:00
-- url     : https://prove2.me/submissions/d105cc83-b53c-4e11-988b-8fac733fb4e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProdEqSumOfFactorwiseLinearExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  intro K _ X I S x a b A B h1 h2 h3 hne
  classical
  have key : ∀ T : Finset K, ∀ q : ∀ n, X n,
      ∑ i ∈ S, x i * ∏ n, (if n ∈ T then b n i else a n i (q n)) =
        ∏ n, (if n ∈ T then B n else A n (q n)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro q; simpa using (h3 q).symm
    | insert m T hm ih =>
      intro q
      obtain ⟨c, hc⟩ : ∃ c, c = ∏ n ∈ univ.erase m, (if n ∈ T then B n else A n (q n)) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : I → ℂ, y = fun i => x i * ∏ n ∈ univ.erase m,
          (if n ∈ T then b n i else a n i (q n)) := ⟨_, rfl⟩
      have hL : ∀ t, ∑ i ∈ S, y i * a m i t = A m t * c := by
        intro t
        have h := ih (Function.update q m t)
        have e1 : ∀ i, ∏ n, (if n ∈ T then b n i else a n i (Function.update q m t n)) =
            a m i t * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
          intro i
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        have e2 : ∏ n, (if n ∈ T then B n else A n (Function.update q m t n)) = A m t * c := by
          rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        rw [e2] at h
        simp only [e1] at h
        rw [← h, hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have e3 : ∀ i, ∏ n, (if n ∈ insert m T then b n i else a n i (q n)) =
          b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
        intro i
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      have e4 : ∏ n, (if n ∈ insert m T then B n else A n (q n)) = B m * c := by
        rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      rw [e4]
      simp only [e3]
      have hs : ∑ i ∈ S, x i * (b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))) =
          ∑ i ∈ S, y i * b m i := by
        rw [hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      by_cases hc0 : c = 0
      · rw [hc0, mul_zero]
        apply h1 m y
        intro t
        rw [hL t, hc0, mul_zero]
      · have hB := h2 m (fun i => y i / c) (by
          intro t
          have : ∑ i ∈ S, y i / c * a m i t = (∑ i ∈ S, y i * a m i t) / c := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [this, hL t, mul_div_cancel_right₀ _ hc0])
        rw [hB, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
  obtain ⟨q⟩ : Nonempty (∀ n, X n) := ⟨fun n => Classical.choice (hne n)⟩
  simpa using (key Finset.univ q).symm
end GlobalTheory
