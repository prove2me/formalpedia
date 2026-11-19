-- Prove2me | solution 1 for Kyprianou.Ch03.exponentRegularity_strictConvexNontrivial
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:16:24.563193+00:00
-- url     : https://prove2.me/submissions/5b15b200-99d4-4679-9352-930057d34d3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace SCVAux

noncomputable def g (θ y : ℝ) : ℝ :=
  Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y

lemma g_bound (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    |g θ y| ≤ (1 + 2 * θ ^ 2) * min 1 (y ^ 2) := by
  unfold g
  by_cases hy1 : -1 < y
  · have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 :=
      Set.indicator_of_mem (show y ∈ Ioo (-1 : ℝ) 1 from ⟨hy1, by linarith⟩) _
    rw [hind, mul_one]
    have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right (by nlinarith)
    rw [hmin]
    by_cases hs : |θ * y| ≤ 1
    · have := Real.abs_exp_sub_one_sub_id_le hs
      have h2 : (θ * y) ^ 2 = θ ^ 2 * y ^ 2 := by ring
      nlinarith [sq_nonneg y, sq_nonneg θ]
    · push Not at hs
      have hneg : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
      have habs : |θ * y| = -(θ * y) := abs_of_nonpos hneg
      rw [habs] at hs
      have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hneg
      have he0 : 0 < Real.exp (θ * y) := Real.exp_pos _
      have hsq : 1 < θ ^ 2 * y ^ 2 := by nlinarith
      have hlin : -(θ * y) < θ ^ 2 * y ^ 2 := by nlinarith
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg y]
  · push Not at hy1
    have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    rw [hind, mul_zero, sub_zero]
    have hmin : min 1 (y ^ 2) = 1 := min_eq_left (by nlinarith)
    rw [hmin]
    have hneg : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
    have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hneg
    have he0 : 0 < Real.exp (θ * y) := Real.exp_pos _
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg θ]

end SCVAux

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ((0 < L.σ ∨ L.ν ≠ 0) →
      StrictConvexOn ℝ (Set.Ioi 0) L.ψ) := by
  intro hcase
  set μ : Measure ℝ := L.ν.restrict (Iio 0) with hμ
  -- integrability of min 1 y^2
  have hmeas_min : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by fun_prop
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) L.ν := by
    refine ⟨hmeas_min.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun y => le_min zero_le_one (sq_nonneg y)))]
    exact L.ν_integrable
  have hg_meas : ∀ θ, Measurable (SCVAux.g θ) := by
    intro θ
    unfold SCVAux.g
    have : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
      measurable_const.indicator measurableSet_Ioo
    fun_prop
  have hg_int : ∀ θ, 0 ≤ θ → Integrable (SCVAux.g θ) μ := by
    intro θ hθ
    refine Integrable.mono' ((hmin_int.restrict).const_mul (1 + 2 * θ ^ 2))
      (hg_meas θ).aestronglyMeasurable ?_
    rw [hμ, ae_restrict_iff' measurableSet_Iio]
    exact Eventually.of_forall (fun y hy => by
      rw [Real.norm_eq_abs]; exact SCVAux.g_bound θ y hθ hy)
  have hψ : ∀ θ, L.ψ θ = L.c * θ + L.σ ^ 2 * θ ^ 2 / 2 + ∫ y, SCVAux.g θ y ∂μ := by
    intro θ; rfl
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx z hz hxz a b ha hb hab
  simp only [smul_eq_mul]
  rw [hψ, hψ, hψ]
  set m := a * x + b * z with hm
  have hx0 : (0:ℝ) ≤ x := le_of_lt hx
  have hz0 : (0:ℝ) ≤ z := le_of_lt hz
  have hm0 : 0 ≤ m := by positivity
  -- pointwise difference
  set Df : ℝ → ℝ := fun y => a * SCVAux.g x y + b * SCVAux.g z y - SCVAux.g m y with hDf
  have hD : ∀ y, Df y = a * Real.exp (x * y) + b * Real.exp (z * y) - Real.exp (m * y) := by
    intro y
    simp only [hDf, SCVAux.g, hm]
    have hb' : b = 1 - a := by linarith
    subst hb'
    ring
  have hDpos : ∀ y, y ≠ 0 → 0 < Df y := by
    intro y hy
    rw [hD]
    have hne : x * y ≠ z * y := by
      intro h; exact hxz (mul_right_cancel₀ hy h)
    have := strictConvexOn_exp.2 (Set.mem_univ (x * y)) (Set.mem_univ (z * y)) hne ha hb hab
    simp only [smul_eq_mul] at this
    have hmy : m * y = a * (x * y) + b * (z * y) := by rw [hm]; ring
    rw [hmy]; linarith
  have hDnn : ∀ y, 0 ≤ Df y := by
    intro y
    by_cases hy : y = 0
    · rw [hD, hy]; simp; linarith
    · exact (hDpos y hy).le
  have hDint : Integrable Df μ :=
    (((hg_int x hx0).const_mul a).add ((hg_int z hz0).const_mul b)).sub (hg_int m hm0)
  have hIeq : ∫ y, Df y ∂μ = a * ∫ y, SCVAux.g x y ∂μ + b * ∫ y, SCVAux.g z y ∂μ -
      ∫ y, SCVAux.g m y ∂μ := by
    have i1 : Integrable (fun y => a * SCVAux.g x y) μ := (hg_int x hx0).const_mul a
    have i2 : Integrable (fun y => b * SCVAux.g z y) μ := (hg_int z hz0).const_mul b
    have i12 : Integrable (fun y => a * SCVAux.g x y + b * SCVAux.g z y) μ := i1.add i2
    simp only [hDf]
    rw [integral_sub i12 (hg_int m hm0), integral_add i1 i2, integral_const_mul,
      integral_const_mul]
  have hInn : 0 ≤ ∫ y, Df y ∂μ := integral_nonneg hDnn
  have hquad : a * x ^ 2 + b * z ^ 2 - m ^ 2 = a * b * (x - z) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hm, hb']; ring
  have hxz2 : 0 < (x - z) ^ 2 := by
    have : x - z ≠ 0 := sub_ne_zero.mpr hxz
    positivity
  have hab0 : 0 < a * b * (x - z) ^ 2 := by positivity
  rcases hcase with hσ | hν
  · have hσ2 : 0 < L.σ ^ 2 := by positivity
    have : 0 < L.σ ^ 2 * (a * b * (x - z) ^ 2) := mul_pos hσ2 hab0
    have hlin : L.c * m = a * (L.c * x) + b * (L.c * z) := by rw [hm]; ring
    nlinarith [hquad, hIeq, hInn]
  · have hνpos : L.ν (Iio 0) ≠ 0 := by
      intro h0
      apply hν
      have hall : L.ν univ = 0 := by
        rw [← Set.Iio_union_Ici (a := (0:ℝ))]
        exact measure_union_null h0 L.ν_Ici
      exact Measure.measure_univ_eq_zero.mp hall
    have hIpos : 0 < ∫ y, Df y ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hDnn hDint]
      have hsub : Iio (0:ℝ) ⊆ Function.support Df := by
        intro y hy
        exact (hDpos y (ne_of_lt hy)).ne'
      have : μ (Iio 0) ≤ μ (Function.support Df) := measure_mono hsub
      rw [hμ, Measure.restrict_apply measurableSet_Iio, Set.inter_self] at this
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hνpos) this
    have hσ2 : 0 ≤ L.σ ^ 2 * (a * b * (x - z) ^ 2) := by positivity
    have hlin : L.c * m = a * (L.c * x) + b * (L.c * z) := by rw [hm]; ring
    nlinarith [hquad, hIeq, hIpos]
