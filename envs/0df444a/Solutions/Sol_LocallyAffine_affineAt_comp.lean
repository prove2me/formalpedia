-- Prove2me | solution 1 for LocallyAffine.affineAt_comp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-14T11:45:00.307218+00:00
-- url     : https://prove2.me/submissions/254d75ef-e833-4101-9510-fdefa38abc95

import Mathlib



/-- Local affineness composes: if `f` agrees with an affine map on a neighbourhood of `x`,
and `g` agrees with an affine map on a neighbourhood of `f x`, then `g ∘ f` agrees with an
affine map on a neighbourhood of `x`. -/
theorem solution {f g : ℝ → ℝ} {x : ℝ}
    (hf : ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    (hg : ∃ δ > 0, ∃ c d : ℝ, ∀ y ∈ Set.Ioo (f x - δ) (f x + δ), g y = c * y + d) :
    ∃ η > 0, ∃ e k : ℝ, ∀ y ∈ Set.Ioo (x - η) (x + η), g (f y) = e * y + k := by
  obtain ⟨ε, hε, a, b, hab⟩ := hf
  obtain ⟨δ, hδ, c, d, hcd⟩ := hg
  have hx : f x = a * x + b := hab x (by constructor <;> linarith)
  refine ⟨min ε (δ / (|a| + 1)), lt_min hε (div_pos hδ (by positivity)), c * a, c * b + d, ?_⟩
  intro y hy
  have hyε : y ∈ Set.Ioo (x - ε) (x + ε) := by
    have := min_le_left ε (δ / (|a| + 1))
    constructor
    · have := hy.1; linarith
    · have := hy.2; linarith
  have hfy : f y = a * y + b := hab y hyε
  have hdist : |f y - f x| < δ := by
    rw [hfy, hx, show a * y + b - (a * x + b) = a * (y - x) by ring, abs_mul]
    have h1 : |y - x| < δ / (|a| + 1) := by
      rw [abs_lt]
      have hm := min_le_right ε (δ / (|a| + 1))
      have := hy.1; have := hy.2
      constructor <;> linarith
    have h2 : |a| * |y - x| ≤ (|a| + 1) * |y - x| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h3 : (|a| + 1) * |y - x| < (|a| + 1) * (δ / (|a| + 1)) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    have h4 : (|a| + 1) * (δ / (|a| + 1)) = δ := by field_simp
    linarith
  have hmem : f y ∈ Set.Ioo (f x - δ) (f x + δ) := by
    rw [abs_lt] at hdist; constructor <;> linarith [hdist.1, hdist.2]
  rw [hcd _ hmem, hfy]; ring


