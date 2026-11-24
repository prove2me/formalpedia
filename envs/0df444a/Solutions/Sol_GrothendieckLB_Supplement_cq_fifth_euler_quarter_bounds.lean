-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_fifth_euler_quarter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:04:29.5429+00:00
-- url     : https://prove2.me/submissions/295eebea-6846-4ca9-aacb-2e4cf1d1e937

import Theorems.Thm_GrothendieckLB_Supplement_cq_quadrant_gaussian_jacobian
import Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_euler_gaussian_majorant
import Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_price_majorant_quarters

open GrothendieckLB.Supplement
namespace GaussianMajorant
private theorem sumNonnegative {α : Type} (xs : List α) (f : α → ℝ) (h : ∀ x, 0≤f x) :
    0≤(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa using add_nonneg (h x) ih
private theorem positive (z : ℂ) : 0≤CQPrice.majorant z := by
  apply sumNonnegative
  intro t
  apply mul_nonneg (norm_nonneg _)
  apply div_nonneg _ (by positivity)
  apply sumNonnegative
  intro e
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
end GaussianMajorant

theorem solution (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t| < 1 → F (t : ℂ) = (cqCorr 0.136419125 0.34101124 0.05276111 t : ℂ))
    (r s θ : ℝ) (hr : (99999 : ℝ) / 100000 ≤ r) (hr₁ : r < 1) (hs : s ∈ Set.Icc 0 1)
    (hθ : let a := 2 * Real.arctan (s^2)
          θ = a ∨ θ = Real.pi-a ∨ θ = Real.pi+a ∨ θ = 2*Real.pi-a) :
    let v := ((2 / Real.pi) * (4*s / (1+s^4))) *
      ‖(((fun g : ℂ → ℂ => fun w : ℂ => w * deriv g w)^[5]) F) (circleMap 0 r θ)‖
    (s ≤ 1/4 → v ≤ 531000) ∧
      (1/4 ≤ s → s ≤ 1/2 → v ≤ 545000) ∧
      (1/2 ≤ s → s ≤ 3/4 → v ≤ 486000) ∧
      (3/4 ≤ s → v ≤ 84000) := by
  let z := circleMap 0 r θ
  let u := CQPrice.majorant (CQPrice.point r s)
  let J := (2/Real.pi)*(4*s/(1+s^4))
  let f := ‖(((fun g : ℂ → ℂ => fun w : ℂ => w * deriv g w)^[5]) F) z‖
  have hj : 0≤J := by dsimp [J]; have := hs.1; positivity
  have hu : 0≤u := GaussianMajorant.positive _
  have hF' : f ≤ (2/Real.sqrt ‖1-z^2‖)*u := cq_fifth_euler_gaussian_majorant F hF hreal r s θ hr hr₁ hs hθ
  have hg : J*(2/Real.sqrt ‖1-z^2‖) ≤ 2.55 := cq_quadrant_gaussian_jacobian r s θ hr hs hθ
  have h : J*f ≤ 2.55*u := by
    calc
      _ ≤ J*((2/Real.sqrt ‖1-z^2‖)*u) := mul_le_mul_of_nonneg_left hF' hj
      _ = (J*(2/Real.sqrt ‖1-z^2‖))*u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hg hu
  obtain ⟨h0,h1,h2,h3⟩ := cq_fifth_price_majorant_quarters r s hr hr₁ hs
  exact ⟨fun h' => h.trans (h0 h'),fun l u' => h.trans (h1 l u'),fun l u' => h.trans (h2 l u'),
    fun h' => h.trans (h3 h')⟩
