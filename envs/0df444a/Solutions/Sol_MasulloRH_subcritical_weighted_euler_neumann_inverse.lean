-- Prove2me | solution 1 for MasulloRH.subcritical_weighted_euler_neumann_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:20:31.800233+00:00
-- url     : https://prove2.me/submissions/ae61082e-7f11-4bc7-b05d-761a5fb628c7

import Mathlib
open Filter Topology
theorem solution (α L : ℝ) (ha : 0 ≤ α) (hc : α < 1/2) (hL : 0 < L) :
    let w := fun x : ℝ => Real.exp (α * |x|) * (1 + x^2)
    let b := fun n : ℕ => sSup (Set.range (fun x : ℝ =>
      Real.exp (-(n:ℝ)*L/2) * w x / w (x+(n:ℝ)*L)))
    Summable b ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (T : E →L[ℝ] E), (∀ n : ℕ, ‖T^n‖ ≤ b n) →
      Summable (fun n : ℕ => ‖T^n‖) ∧
      (1-T)*(∑' n : ℕ, T^n) = 1 ∧ (∑' n : ℕ, T^n)*(1-T) = 1 := by
  dsimp only
  let r : ℝ := Real.exp ((α-1/2)*L)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hc) hL)
  let R := fun (n : ℕ) (x : ℝ) =>
    Real.exp (-(n:ℝ)*L/2) * (Real.exp (α*|x|)*(1+x^2)) /
      (Real.exp (α*|x+(n:ℝ)*L|)*(1+(x+(n:ℝ)*L)^2))
  let B := fun n : ℕ => 2*r^n + (2*L^2)*((n:ℝ)^2*r^n)
  have bound (n : ℕ) (x : ℝ) : R n x ≤ B n := by
    let y := (n:ℝ)*L
    have hy : 0 ≤ y := mul_nonneg (Nat.cast_nonneg n) hL.le
    have hab : |x| ≤ |x+y|+y := by
      simpa [abs_of_nonneg hy] using abs_sub (x+y) y
    have hex : Real.exp (-(n:ℝ)*L/2) * Real.exp (α*|x|) ≤
        r^n * Real.exp (α*|x+y|) := by
      dsimp [r]
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hab ha
      dsimp [y] at *
      nlinarith
    have hpol : 1+x^2 ≤ (2+2*y^2)*(1+(x+y)^2) := by
      nlinarith [sq_nonneg (x+2*y), sq_nonneg (x+y), mul_nonneg (sq_nonneg y) (sq_nonneg (x+y))]
    have hx := mul_le_mul hex hpol (by positivity) (by positivity)
    dsimp only [R,B]
    apply (div_le_iff₀ (by positivity)).mpr
    change Real.exp (-(n:ℝ)*L/2) * (Real.exp (α*|x|)*(1+x^2)) ≤ _
    dsimp only [y] at hx
    linarith only [hx]
  have hB : Summable B := by
    exact ((summable_geometric_of_lt_one hr0.le hr1).mul_left 2).add
      ((summable_pow_mul_geometric_of_norm_lt_one 2 (by simpa [Real.norm_eq_abs, abs_of_pos hr0] using hr1 : ‖r‖ < 1)).mul_left (2*L^2))
  have hR (n : ℕ) : BddAbove (Set.range (R n)) := ⟨B n, by rintro _ ⟨x,rfl⟩; exact bound n x⟩
  have hs : Summable (fun n => sSup (Set.range (R n))) := by
    apply Summable.of_nonneg_of_le _ _ hB
    · intro n
      exact le_trans (show 0 ≤ R n 0 by dsimp [R]; positivity) (le_csSup (hR n) ⟨0,rfl⟩)
    · intro n
      exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨x,rfl⟩; exact bound n x)
  refine ⟨hs,?_⟩
  intro E _ _ _ T ht
  have hnorm : Summable (fun n : ℕ => ‖T^n‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ht hs
  exact ⟨hnorm, hnorm.of_norm.one_sub_mul_tsum_pow, hnorm.of_norm.tsum_pow_mul_one_sub⟩
