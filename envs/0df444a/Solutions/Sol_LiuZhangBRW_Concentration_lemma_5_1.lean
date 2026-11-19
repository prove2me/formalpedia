-- Prove2me | solution 1 for LiuZhangBRW.Concentration.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:03:58.385047+00:00
-- url     : https://prove2.me/submissions/7885f558-4c0f-4c5e-83fb-08153efec1a6

import Mathlib

open MeasureTheory

lemma exp_tail_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2).factorial : ℝ)) (Real.exp x - 1 - x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  have e : Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i.factorial : ℝ) = Real.exp x - 1 - x := by
    simp [Finset.sum_range_succ]; ring
  rw [e] at h2; exact h2

lemma phi_scale (l w : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hw : 0 ≤ w) :
    Real.exp (l * w) - 1 - l * w ≤ l ^ 2 * (Real.exp w - 1 - w) := by
  have h1 := exp_tail_hasSum (l * w)
  have h2 := (exp_tail_hasSum w).mul_left (l ^ 2)
  refine hasSum_le (fun n => ?_) h1 h2
  rw [mul_pow, mul_div_assoc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc l ^ (n + 2) = l ^ 2 * l ^ n := by ring
    _ ≤ l ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hl0 hl1) (by positivity)
    _ = l ^ 2 := mul_one _

lemma phi_abs (y : ℝ) : Real.exp y - 1 - y ≤ Real.exp |y| - 1 - |y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    -- e^y - y ≤ e^{-y} + y for y ≤ 0
    have hs := Real.sinh_le_self_iff.mpr h
    rw [Real.sinh_eq] at hs
    linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hmean : ∫ ω, X ω ∂μ = 0) (δ t : ℝ) (hδ : 0 < δ)
    (ht : |t| / δ ≤ 1) (hexp : Integrable (fun ω => Real.exp (δ * |X ω|)) μ) :
    ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 / δ ^ 2 * ∫ ω, Real.exp (δ * |X ω|) ∂μ) := by
  set s := |t| / δ with hs
  have hs0 : 0 ≤ s := by positivity
  have htδ : |t| ≤ δ := by rwa [hs, div_le_one hδ] at ht
  have hpt : ∀ ω, Real.exp (t * X ω) ≤ 1 + t * X ω + s ^ 2 * Real.exp (δ * |X ω|) := by
    intro ω
    have h1 := phi_abs (t * X ω)
    have habs : |t * X ω| = s * (δ * |X ω|) := by
      rw [abs_mul, hs]; field_simp
    rw [habs] at h1
    have h2 := phi_scale s (δ * |X ω|) hs0 ht (by positivity)
    have h3 : s ^ 2 * (Real.exp (δ * |X ω|) - 1 - δ * |X ω|) ≤ s ^ 2 * Real.exp (δ * |X ω|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 0 ≤ δ * |X ω| := by positivity
      linarith
    linarith
  have hXi : Integrable X μ := by
    refine Integrable.mono' (hexp.div_const δ) hX.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, le_div_iff₀ hδ]
    have := Real.add_one_le_exp (δ * |X ω|)
    nlinarith [abs_nonneg (X ω)]
  have hEi : Integrable (fun ω => Real.exp (t * X ω)) μ := by
    refine Integrable.mono' hexp (by fun_prop) (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc t * X ω ≤ |t * X ω| := le_abs_self _
      _ = |t| * |X ω| := abs_mul _ _
      _ ≤ δ * |X ω| := mul_le_mul_of_nonneg_right htδ (abs_nonneg _)
  calc ∫ ω, Real.exp (t * X ω) ∂μ
      ≤ ∫ ω, (1 + t * X ω + s ^ 2 * Real.exp (δ * |X ω|)) ∂μ :=
        integral_mono hEi (((integrable_const 1).add (hXi.const_mul t)).add (hexp.const_mul _)) hpt
    _ = 1 + s ^ 2 * ∫ ω, Real.exp (δ * |X ω|) ∂μ := by
        rw [integral_add (f := fun ω => 1 + t * X ω) (g := fun ω => s ^ 2 * Real.exp (δ * |X ω|))
          (by exact (integrable_const 1).add (hXi.const_mul t)) (by exact hexp.const_mul _),
          integral_add (f := fun _ => (1:ℝ)) (g := fun ω => t * X ω) (integrable_const 1)
          (by exact hXi.const_mul t), integral_const_mul, integral_const_mul, hmean]
        simp
    _ ≤ Real.exp (s ^ 2 * ∫ ω, Real.exp (δ * |X ω|) ∂μ) := by
        have := Real.add_one_le_exp (s ^ 2 * ∫ ω, Real.exp (δ * |X ω|) ∂μ); linarith
    _ = _ := by
        congr 1; rw [hs, div_pow, sq_abs]
