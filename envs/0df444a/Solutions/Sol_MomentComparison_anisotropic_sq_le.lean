-- Prove2me | solution 1 for MomentComparison.anisotropic_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:59:19.313972+00:00
-- url     : https://prove2.me/submissions/af07b379-221b-48f0-bea8-e46d22839713

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Lens
section
public section
namespace MomentComparison
private theorem normSq_le_square {w : ℂ} {r : ℝ} (h : ‖w‖ ≤ r) :
    w.re ^ 2 + w.im ^ 2 ≤ r ^ 2 := by
  have hn := norm_nonneg w
  have he := Complex.sq_norm w
  rw [Complex.normSq_apply] at he
  nlinarith
private theorem lens_coordinate_bound {p : ℝ} (hp : 2 < p) {w : ℂ}
    (hw : inLens p w) :
    let a : ℝ := (p - 1)⁻¹
    w.re ^ 2 + w.im ^ 2 + (1 - a) * |w.re| ≤ a := by
  let a : ℝ := (p - 1)⁻¹
  have hsub : (p - 2) / (2 * (p - 1)) = (1 - a) / 2 := by
    dsimp [a]
    field_simp [show p - 1 ≠ 0 by linarith]
    ring
  have hadd : p / (2 * (p - 1)) = (1 + a) / 2 := by
    dsimp [a]
    field_simp [show p - 1 ≠ 0 by linarith]
    ring
  obtain ⟨hm, ha⟩ := hw
  rw [hsub, hadd] at hm ha
  have hm' := normSq_le_square hm
  have ha' := normSq_le_square ha
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero] at hm' ha'
  change w.re ^ 2 + w.im ^ 2 + (1 - a) * |w.re| ≤ a
  rcases le_total 0 w.re with h | h
  · rw [abs_of_nonneg h]
    nlinarith only [ha']
  · rw [abs_of_nonpos h]
    nlinarith only [hm']
private theorem quadratic_nonneg {A B D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hdet : 0 ≤ A * D - B ^ 2) (x y : ℝ) :
    0 ≤ A * x ^ 2 + 2 * B * x * y + D * y ^ 2 := by
  rcases hA.eq_or_lt with hA | hA
  · have hB : B = 0 := by
      rw [← hA, zero_mul, zero_sub] at hdet
      nlinarith [sq_nonneg B]
    rw [← hA, hB]
    simpa using mul_nonneg hD (sq_nonneg y)
  · apply nonneg_of_mul_nonneg_left _ hA
    calc
      0 ≤ (A * x + B * y) ^ 2 + (A * D - B ^ 2) * y ^ 2 := by positivity
      _ = _ := by ring
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 2 < p) {w z : ℂ} (hw : inLens p w) :
    (p - 1) * (w * z).re ^ 2 + (w * z).im ^ 2 ≤
      (p - 1)⁻¹ * z.re ^ 2 + z.im ^ 2 := by
  let a : ℝ := (p - 1)⁻¹
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr (by linarith)
  have ha1 : a ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by linarith)
  have hcoord := lens_coordinate_bound hp hw
  change w.re ^ 2 + w.im ^ 2 + (1 - a) * |w.re| ≤ a at hcoord
  let u := w.re
  let v := w.im
  let t := a - u ^ 2 - v ^ 2
  let A := a ^ 2 - u ^ 2 - a * v ^ 2
  let D := a - v ^ 2 - a * u ^ 2
  let B := (1 - a) * u * v
  have ht : (1 - a) * |u| ≤ t := by dsimp [t, u, v]; linarith
  have ht0 : 0 ≤ t := le_trans (mul_nonneg (sub_nonneg.mpr ha1) (abs_nonneg _)) ht
  have hu : |u| ≤ a := by
    by_contra! h
    have hp0 := mul_pos (sub_pos.mpr h) (by positivity : 0 < 1 + |u|)
    have he : (|u| - a) * (1 + |u|) = u ^ 2 + (1 - a) * |u| - a := by
      rw [← sq_abs u]
      ring
    dsimp [t] at ht
    rw [he] at hp0
    nlinarith [sq_nonneg v]
  have hA : 0 ≤ A := by
    have h₁ := mul_le_mul_of_nonneg_left ht ha.le
    have h₂ := mul_nonneg (sub_nonneg.mpr ha1)
      (mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hu))
    have he : A = a * t - a * ((1 - a) * |u|) + (1 - a) * (|u| * (a - |u|)) := by
      dsimp [A, t]
      conv_lhs => rw [← sq_abs u]
      conv_rhs => rw [← sq_abs u]
      ring
    rw [he]
    linarith
  have hD : 0 ≤ D := by
    have he : D = t + (1 - a) * u ^ 2 := by dsimp [D, t]; ring
    rw [he]
    positivity
  have hdet : 0 ≤ A * D - B ^ 2 := by
    have he : A * D - B ^ 2 =
        a * ((t - (1 - a) * |u|) * (t + (1 - a) * |u|)) := by
      calc
        _ = a * (t ^ 2 - (1 - a)^2 * u^2) := by dsimp [A, D, B, t]; ring
        _ = _ := by rw [← sq_abs u]; ring
    rw [he]
    exact mul_nonneg ha.le
      (mul_nonneg (sub_nonneg.mpr ht) (add_nonneg ht0
        (mul_nonneg (sub_nonneg.mpr ha1) (abs_nonneg _))))
  have hq := quadratic_nonneg hA hD hdet z.re z.im
  have hay : a * (p - 1) = 1 := inv_mul_cancel₀ (by linarith)
  apply le_of_mul_le_mul_left _ ha
  simp only [Complex.mul_re, Complex.mul_im]
  change a * ((p - 1) * (u * z.re - v * z.im) ^ 2 +
      (u * z.im + v * z.re) ^ 2) ≤ a * (a * z.re ^ 2 + z.im ^ 2)
  rw [mul_add, ← mul_assoc, hay, one_mul]
  have he : a * (a * z.re ^ 2 + z.im ^ 2) -
      ((u * z.re - v * z.im) ^ 2 + a * (u * z.im + v * z.re) ^ 2) =
      A * z.re ^ 2 + 2 * B * z.re * z.im + D * z.im ^ 2 := by
    dsimp [A, B, D]
    ring
  rw [← he] at hq
  exact sub_nonneg.mp hq
end MomentComparison
