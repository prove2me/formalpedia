-- Prove2me | solution 1 for LeviSampling.BaseStock.min_above_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:28:47.214838+00:00
-- url     : https://prove2.me/submissions/cc9867b5-50e2-4b7e-8c95-a35ab16aa5bc

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Model

open LeviSampling.BaseStock
/-- **Fact 3.1** (Levi, Roundy & Shmoys 2007, p. 828). Let `f : ℝ → ℝ` be convex with a
minimizer `r`. Then `w(x) = min_{y ≥ x} f(y)` is convex, `w(x) = f(r)` for `x ≤ r`, and
`w(x) = f(x)` for `x > r`. -/
theorem solution (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r : ℝ)
    (hr : ∀ y, f r ≤ f y) :
    ConvexOn ℝ Set.univ (minAbove f) ∧
      (∀ x, x ≤ r → minAbove f x = f r) ∧
      (∀ x, r < x → minAbove f x = f x) := by
  have hmono : ∀ x y, r ≤ x → x ≤ y → f x ≤ f y := by
    intro x y hx hxy
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    rcases eq_or_lt_of_le hx with h' | h'
    · rw [← h']; exact hr y
    -- x = θ r + (1-θ) y
    have hθ : 0 < y - r := by linarith
    have := hf.2 (Set.mem_univ r) (Set.mem_univ y)
      (show (0:ℝ) ≤ (y - x) / (y - r) from div_nonneg (by linarith) hθ.le)
      (show (0:ℝ) ≤ (x - r) / (y - r) from div_nonneg (by linarith) hθ.le) (by field_simp [hθ.ne']; ring)
    have e : (y - x) / (y - r) * r + (x - r) / (y - r) * y = x := by
      field_simp [hθ.ne']; ring
    simp only [smul_eq_mul] at this
    rw [e] at this
    have h1 := hr y
    have : f x ≤ (y - x) / (y - r) * f y + (x - r) / (y - r) * f y := by
      have := mul_le_mul_of_nonneg_left h1 (div_nonneg (show (0:ℝ) ≤ y - x by linarith) hθ.le)
      linarith
    rw [← add_mul, show (y - x) / (y - r) + (x - r) / (y - r) = 1 by field_simp [hθ.ne']; ring, one_mul] at this
    exact this
  have hbdd : ∀ x : ℝ, BddBelow (Set.range fun y : ↥(Set.Ici x) => f y.1) :=
    fun x => ⟨f r, by rintro _ ⟨y, rfl⟩; exact hr y.1⟩
  have hw : ∀ x, minAbove f x = f (max x r) := by
    intro x
    unfold minAbove
    apply le_antisymm
    · exact ciInf_le (hbdd x) ⟨max x r, Set.mem_Ici.2 (le_max_left _ _)⟩
    · refine le_ciInf fun ⟨y, hy⟩ => ?_
      simp only
      rcases le_total x r with h | h
      · rw [max_eq_right h]; exact hr y
      · rw [max_eq_left h]; exact hmono x y h hy
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [hw, smul_eq_mul]
    have hm : max (a * x + b * y) r ≤ a * max x r + b * max y r := by
      apply max_le
      · nlinarith [le_max_left x r, le_max_left y r]
      · have := mul_le_mul_of_nonneg_left (le_max_right x r) ha
        have := mul_le_mul_of_nonneg_left (le_max_right y r) hb
        have : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
        linarith
    calc f (max (a * x + b * y) r) ≤ f (a * max x r + b * max y r) :=
          hmono _ _ (le_max_right _ _) hm
      _ ≤ a * f (max x r) + b * f (max y r) := by
          have := hf.2 (Set.mem_univ (max x r)) (Set.mem_univ (max y r)) ha hb hab
          simpa [smul_eq_mul] using this
  · intro x hx; rw [hw, max_eq_right hx]
  · intro x hx; rw [hw, max_eq_left hx.le]


