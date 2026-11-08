-- Prove2me | solution 1 for GeomDRSub.lemma_A_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T15:32:49.586503+00:00
-- url     : https://prove2.me/submissions/16313a24-c530-4040-a343-ad64202e3fb8

import Mathlib

/-- Lemma A.1(ii): summation by parts, and the bound under monotone weights. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) (w a : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 n, w k * (a k - a (k - 1)) =
        w n * a n - w 1 * a 0 -
          ∑ k ∈ Finset.Icc 1 (n - 1), (w (k + 1) - w k) * a k) ∧
      ∀ W : ℝ, 0 ≤ w 1 → (∀ k, 1 ≤ k → k < n → w k ≤ w (k + 1)) → w n ≤ W →
        (∀ k ≤ n, 0 ≤ a k) →
        ∑ k ∈ Finset.Icc 1 n, w k * (a k - a (k - 1)) ≤ W * a n := by
  have key : ∀ m : ℕ, 1 ≤ m → ∀ w a : ℕ → ℝ,
      ∑ k ∈ Finset.Icc 1 m, w k * (a k - a (k - 1)) =
        w m * a m - w 1 * a 0 -
          ∑ k ∈ Finset.Icc 1 (m - 1), (w (k + 1) - w k) * a k := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        intro w a
        simp
        ring
    | succ m hm ih =>
        intro w a
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        rw [ih]
        have hsub : m + 1 - 1 = m := rfl
        rw [hsub]
        have htop := Finset.sum_Icc_succ_top (a := 1) (b := m - 1)
          (f := fun k => (w (k + 1) - w k) * a k) (by omega : 1 ≤ m - 1 + 1)
        rw [Nat.sub_add_cancel hm] at htop
        rw [htop]
        ring
  constructor
  · exact key n hn w a
  · intro W hw1 hmono hWn ha
    rw [key n hn w a]
    have h1 : 0 ≤ w 1 * a 0 := mul_nonneg hw1 (ha 0 (by omega))
    have h2 : 0 ≤ ∑ k ∈ Finset.Icc 1 (n - 1), (w (k + 1) - w k) * a k := by
      apply Finset.sum_nonneg
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hle : w k ≤ w (k + 1) := hmono k hk.1 (by omega)
      have hak : 0 ≤ a k := ha k (by omega)
      nlinarith
    have h3 : w n * a n ≤ W * a n := by
      have han : 0 ≤ a n := ha n (le_refl n)
      nlinarith
    linarith
