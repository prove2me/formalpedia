-- Prove2me | solution 1 for Milne.zeta_p1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:15:11.801312+00:00
-- url     : https://prove2.me/submissions/6be938ac-453f-4e23-9c0f-7000c854b66f

import Mathlib
import Definitions.Def_Milne_zeta

open Milne

namespace A3ZetaP1

/-- partial geometric sums `G k = ∑_{i ≤ k} p^i` -/
noncomputable def G (p : ℕ) (k : ℕ) : ℚ := ∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ i

lemma split (p n j : ℕ) (hj : j ≤ n) :
    (p : ℚ) ^ (n + 1 - j) * G p j + G p (n - j) = G p (n + 1) := by
  unfold G
  have h : n + 1 + 1 = (n - j + 1) + (j + 1) := by omega
  rw [h, Finset.sum_range_add (fun i => (p : ℚ) ^ i) (n - j + 1) (j + 1), Finset.mul_sum,
    add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← pow_add]
  congr 1
  omega

lemma recurrence (p n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (1 + (p : ℚ) ^ (n + 1 - j)) * G p j
      = (n + 1 : ℚ) * G p (n + 1) := by
  have h1 : ∀ j ∈ Finset.range (n + 1),
      (1 + (p : ℚ) ^ (n + 1 - j)) * G p j = G p j + (G p (n + 1) - G p (n - j)) := by
    intro j hj
    have := split p n j (by simp at hj; omega)
    linarith [this]
  have hr : ∑ x ∈ Finset.range (n + 1), G p (n - x) = ∑ x ∈ Finset.range (n + 1), G p x := by
    have := Finset.sum_range_reflect (fun j => G p j) (n + 1)
    simpa using this
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hr]
  simp

lemma prefix_eq (p : ℕ) (n : ℕ) :
    ∀ k ≤ n, zetaSeq (fun m => (1 : ℚ) + (p : ℚ) ^ m) n k = G p k := by
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst this
    simp [zetaSeq, G]
  | succ n ih =>
    intro k hk
    simp only [zetaSeq]
    split
    · exact ih k (by assumption)
    · have hk' : k = n + 1 := by omega
      subst hk'
      have hs : ∑ j ∈ Finset.range (n + 1),
          ((1 : ℚ) + (p : ℚ) ^ (n + 1 - j)) * zetaSeq (fun m => (1 : ℚ) + (p : ℚ) ^ m) n j
          = ∑ j ∈ Finset.range (n + 1), (1 + (p : ℚ) ^ (n + 1 - j)) * G p j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j (by simp at hj; omega)]
      rw [hs, recurrence]
      have hn : (n + 1 : ℚ) ≠ 0 := by positivity
      field_simp

end A3ZetaP1

theorem solution (p : ℕ) (n : ℕ) :
    zetaCoeff (fun m => (1 : ℚ) + (p : ℚ) ^ m) n
      = ∑ k ∈ Finset.range (n + 1), (p : ℚ) ^ k := by
  exact A3ZetaP1.prefix_eq p (n + 1) n (by omega)
