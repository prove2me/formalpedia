-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_sum_component
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:41:05.798982+00:00
-- url     : https://prove2.me/submissions/ea2d81de-7185-4b90-a422-890936958e3d

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ)
    (hw : ∀ i, 0 < (w i : ℝ))
    (i : Fin d) (K : Nat) (c : Fin (K + 1) → ℂ)
    (n : Fin (K + 1)) :
    MvPolynomial.weightedHomogeneousComponent w
      (((n : ℕ) : ℚ) * w i)
      (∑ k : Fin (K + 1), MvPolynomial.C (c k) *
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (k : Nat)) =
      MvPolynomial.C (c n) * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat) := by
  classical
  let P : Fin (K + 1) → MvPolynomial (Fin d) ℂ := fun k =>
    MvPolynomial.C (c k) * (MvPolynomial.X i) ^ (k : Nat)
  have hpow : ∀ k : ℕ,
      MvPolynomial.IsWeightedHomogeneous w ((MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ k) ((k : ℚ) * w i) := by
    intro k
    induction k with
    | zero => simp [MvPolynomial.isWeightedHomogeneous_one]
    | succ k ih =>
        rw [pow_succ]
        have hx := MvPolynomial.isWeightedHomogeneous_X ℂ w i
        convert ih.mul hx using 1 <;> push_cast <;> ring
  have hP (k : Fin (K + 1)) :
      (P k).IsWeightedHomogeneous w (((k : ℕ) : ℚ) * w i) := by
    dsimp [P]
    convert (MvPolynomial.isWeightedHomogeneous_C w (c k)).mul (hpow k) using 1 <;>
      simp
  have hweight (k : Fin (K + 1)) :
      (((n : ℕ) : ℚ) * w i = ((k : ℕ) : ℚ) * w i) ↔ n = k := by
    constructor
    · intro h
      have hwi : (0 : ℚ) < w i := by exact_mod_cast hw i
      have hcast : (n : ℚ) = (k : ℚ) :=
        (mul_right_cancel₀ (ne_of_gt hwi)) h
      exact Fin.ext (Nat.cast_injective hcast)
    · rintro rfl
      rfl
  have hterm (k : Fin (K + 1)) :
      MvPolynomial.weightedHomogeneousComponent w (((n : ℕ) : ℚ) * w i) (P k) =
        if k = n then P n else 0 := by
    by_cases h : k = n
    · subst k
      rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (hP n)]
      simp
    · have hne : (((n : ℕ) : ℚ) * w i) ≠ (((k : ℕ) : ℚ) * w i) := by
        intro heq
        exact h ((hweight k).mp heq |>.symm)
      rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
        (((n : ℕ) : ℚ) * w i) (hP k) hne]
      simp [h]
  change MvPolynomial.weightedHomogeneousComponent w (((n : ℕ) : ℚ) * w i)
      (∑ k : Fin (K + 1), P k) = P n
  rw [map_sum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    simp [hkn]
  · intro hn
    exact (hn (Finset.mem_univ n)).elim