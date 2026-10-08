-- Prove2me | solution 1 for LostSalesBalancing.DualBalancing.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:50:38.654159+00:00
-- url     : https://prove2.me/submissions/e54793fd-059f-4fdc-9fe8-8643676c596d

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model
open Finset LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

private lemma sum_extend (f : ℤ → ℝ) (a b : ℤ) (h : a ≤ b + 1) :
    ∑ j ∈ Icc a (b + 1), f j = (∑ j ∈ Icc a b, f j) + f (b + 1) := by
  have he : Icc a (b + 1) = insert (b + 1) (Icc a b) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  rw [he, sum_insert (by simp)]
  ring

private lemma inventory_step (I : LSInstance) (d Q : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r) :
    onHand I d Q (r + 1) = onHand I d Q r - d r + lostUnits I d Q r +
      order I.toInstance Q (r + 1 - I.L) := by
  have hn : r.toNat = (r - 1).toNat + 1 := by omega
  have hc : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
  have he : onHand I d Q (r + 1) =
      max (onHand I d Q r - d r) 0 + order I.toInstance Q (r + 1 - I.L) := by
    simp only [onHand, show r + 1 - 1 = r by omega, hn, onHandNat, hc]
    congr 2 <;> congr 1 <;> ring
  rw [he, lostUnits]
  by_cases h : d r ≤ onHand I d Q r
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

private lemma inventory_sum (I : LSInstance) (d Q : ℤ → ℝ) (s : ℤ) (hs : 1 ≤ s) (k : ℕ) :
    onHand I d Q (s + k) =
      onHand I d Q s + (∑ j ∈ Icc (s + 1 - I.L) (s + k - I.L), order I.toInstance Q j) -
      (∑ r ∈ Icc s (s + k - 1), d r) +
      ∑ r ∈ Icc s (s + k - 1), lostUnits I d Q r := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    have h1 : Icc (s + 1 - (I.L : ℤ)) (s - I.L) = ∅ := by
      apply Icc_eq_empty_of_lt; omega
    have h2 : Icc s (s - 1) = ∅ := by
      apply Icc_eq_empty_of_lt; omega
    simp [h1, h2]
  | succ k ih =>
    rw [Nat.cast_succ]
    rw [show s + ((k : ℤ) + 1) = (s + k) + 1 by ring, inventory_step I d Q (s + k) (by omega), ih]
    rw [show s + (k : ℤ) + 1 - (I.L : ℤ) = (s + k - I.L) + 1 by ring,
      show s + (k : ℤ) + 1 - 1 = (s + k - 1) + 1 by ring]
    rw [sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega)]
    simp only [show s + (k : ℤ) - 1 + 1 = s + k by ring,
      show s + (k : ℤ) - (I.L : ℤ) + 1 = s + k + 1 - I.L by ring]
    ring


open Finset LeviBalancing.DualBalancing

/-- Equation (11), expressed in lost units so it remains valid for varying or zero penalties. -/
theorem solution (I : LSInstance) (d Q : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hQ : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ Q j)
    (t s : ℤ) (ht : 1 ≤ t) (hs : t ≤ s) (hst : s ≤ t + I.L)
    (hT : t + I.L ≤ (I.T : ℤ)) :
    onHand I d Q (t + I.L) =
      truncPos I d Q s t - cumDemand d s (t + I.L - 1) +
        ∑ r ∈ Icc s (t + I.L - 1), lostUnits I d Q r := by
  have he := inventory_sum I d Q s (by omega) (t + I.L - s).toNat
  have hc : ((t + (I.L : ℤ) - s).toNat : ℤ) = t + I.L - s :=
    Int.toNat_of_nonneg (by omega)
  rw [hc, show s + (t + (I.L : ℤ) - s) = t + I.L by ring] at he
  simpa only [truncPos, cumDemand, max_eq_left (by omega : (1 : ℤ) ≤ s),
    show t + (I.L : ℤ) - I.L = t by ring] using he



#print axioms solution
