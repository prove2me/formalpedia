-- Prove2me | solution 1 for Kyprianou.Ch03.esscherSpectralWitness_property1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:43:50.790837+00:00
-- url     : https://prove2.me/submissions/2efe5fdd-fbba-4b62-80ef-469b1a4c95f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace ESWAux
open Set

/-- for x ≤ 0, e^x - 1 - x ≤ x^2/2 -/
lemma exp_quad_le {x : ℝ} (hx : x ≤ 0) : Real.exp x - 1 - x ≤ x ^ 2 / 2 := by
  set u := -x with hu
  have hu0 : 0 ≤ u := by linarith
  have h1 : 1 + u + u ^ 2 / 2 ≤ Real.exp u := Real.quadratic_le_exp_of_nonneg hu0
  have hE : Real.exp x * Real.exp u = 1 := by
    rw [← Real.exp_add, hu, add_neg_cancel, Real.exp_zero]
  have hEpos : 0 < Real.exp x := Real.exp_pos x
  have hD : 0 < 1 + u + u ^ 2 / 2 := by positivity
  have h2 : Real.exp x * (1 + u + u ^ 2 / 2) ≤ 1 := by
    calc Real.exp x * (1 + u + u ^ 2 / 2) ≤ Real.exp x * Real.exp u :=
          mul_le_mul_of_nonneg_left h1 hEpos.le
      _ = 1 := hE
  have h3 : 1 ≤ (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) := by nlinarith [sq_nonneg (u ^ 2)]
  have h4 : Real.exp x ≤ 1 - u + u ^ 2 / 2 := by
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc hD
    linarith
  have hxu : x = -u := by rw [hu]; ring
  have hx2 : x ^ 2 / 2 = u ^ 2 / 2 := by rw [hxu]; ring
  rw [hx2]; linarith

lemma exp_sub_one_sub_nonneg (x : ℝ) : 0 ≤ Real.exp x - 1 - x := by
  linarith [Real.add_one_le_exp x]

noncomputable def ind (y : ℝ) : ℝ := (Ioo (-1 : ℝ) 1).indicator 1 y

lemma ind_meas : Measurable ind :=
  (measurable_const.indicator measurableSet_Ioo)

lemma min_integrable (ν : Measure ℝ) (h : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤) :
    Integrable (fun y : ℝ => min 1 (y ^ 2)) ν := by
  refine ⟨by fun_prop, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ y : ℝ, ‖min 1 (y ^ 2)‖ₑ = ENNReal.ofReal (min 1 (y ^ 2)) := fun y =>
    Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))
  simp_rw [this]; exact h

lemma g_int (ν : Measure ℝ) (h : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun y => Real.exp (a * y) - 1 - a * y * ind y) (Iio 0) ν := by
  have hm := (min_integrable ν h).integrableOn (s := Iio 0)
  refine Integrable.mono' (hm.const_mul (1 + a ^ 2)) (by have hi := ind_meas; exact Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Iio).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : y < 0 := hy
  rw [Real.norm_eq_abs]
  by_cases hy1 : -1 < y
  · have hind : ind y = 1 := by
      unfold ind; rw [indicator_of_mem (show y ∈ Ioo (-1:ℝ) 1 from ⟨hy1, by linarith⟩)]; rfl
    rw [hind, mul_one]
    have hay : a * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hy0.le
    have hq := exp_quad_le hay
    have hn := exp_sub_one_sub_nonneg (a * y)
    have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right (by nlinarith)
    rw [hmin, abs_of_nonneg hn]
    have : (a * y) ^ 2 / 2 ≤ (1 + a ^ 2) * y ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg a]
    linarith
  · have hind : ind y = 0 := by
      unfold ind; rw [indicator_of_notMem (fun h => hy1 h.1)]
    rw [hind, mul_zero, sub_zero]
    have hmin : min 1 (y ^ 2) = 1 := min_eq_left (by nlinarith)
    rw [hmin]
    have he : Real.exp (a * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 : 0 < Real.exp (a * y) := Real.exp_pos _
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg a]

lemma f3_int (ν : Measure ℝ) (h : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun y => (Real.exp (b * y) - 1) * y * ind y) (Iio 0) ν := by
  have hm := (min_integrable ν h).integrableOn (s := Iio 0)
  refine Integrable.mono' (hm.const_mul b) (by have hi := ind_meas; exact Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Iio).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : y < 0 := hy
  rw [Real.norm_eq_abs]
  by_cases hy1 : -1 < y
  · have hind : ind y = 1 := by
      unfold ind; rw [indicator_of_mem (show y ∈ Ioo (-1:ℝ) 1 from ⟨hy1, by linarith⟩)]; rfl
    rw [hind, mul_one]
    have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right (by nlinarith)
    rw [hmin]
    have h1 : Real.exp (b * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : b * y + 1 ≤ Real.exp (b * y) := Real.add_one_le_exp _
    have : (Real.exp (b * y) - 1) * y = (1 - Real.exp (b * y)) * (-y) := by ring
    rw [this, abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
    nlinarith
  · have hind : ind y = 0 := by
      unfold ind; rw [indicator_of_notMem (fun h => hy1 h.1)]
    rw [hind, mul_zero, abs_zero]
    have : 0 ≤ min 1 (y ^ 2) := le_min zero_le_one (sq_nonneg y)
    positivity

lemma core (c σ β θ : ℝ) (ν : Measure ℝ) (hβ : 0 ≤ β) (hθ : -β ≤ θ)
    (hνIci : ν (Ici 0) = 0) (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤) :
    laplaceExponent (c + β * σ ^ 2 + ∫ x in {x : ℝ | |x| < 1}, (Real.exp (β * x) - 1) * x ∂ν) σ
      (ν.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (β * x)))) θ =
    laplaceExponent c σ ν (θ + β) - laplaceExponent c σ ν β := by
  have hc : ∫ x in {x : ℝ | |x| < 1}, (Real.exp (β * x) - 1) * x ∂ν =
      ∫ y in Iio 0, (Real.exp (β * y) - 1) * y * ind y ∂ν := by
    have e1 : (fun y : ℝ => (Real.exp (β * y) - 1) * y * ind y) =
        (Ioo (-1:ℝ) 1).indicator (fun y => (Real.exp (β * y) - 1) * y) := by
      funext y; unfold ind
      by_cases hy : y ∈ Ioo (-1:ℝ) 1
      · rw [indicator_of_mem hy, indicator_of_mem hy]; simp
      · rw [indicator_of_notMem hy, indicator_of_notMem hy]; simp
    rw [e1, setIntegral_indicator measurableSet_Ioo]
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · refine measure_mono_null (fun y hy => ?_) hνIci
      simp only [mem_diff, mem_setOf_eq, mem_inter_iff, mem_Iio, mem_Ioo, not_and] at hy
      obtain ⟨h1, h2⟩ := hy
      rw [abs_lt] at h1
      simp only [mem_Ici]
      by_contra hneg; push Not at hneg
      exact h2 hneg h1.1 h1.2
    · refine measure_mono_null (fun y hy => ?_) (measure_empty (μ := ν))
      simp only [mem_diff, mem_setOf_eq, mem_inter_iff, mem_Iio, mem_Ioo] at hy
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hy
      exact absurd (abs_lt.2 ⟨h2, h3⟩) h4
  have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (β * x))) := by fun_prop
  unfold laplaceExponent
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hfm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Iio, hc]
  have hpt : ∀ y : ℝ, (ENNReal.ofReal (Real.exp (β * y))).toReal •
      (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) =
      (Real.exp ((θ + β) * y) - 1 - (θ + β) * y * ind y) -
      (Real.exp (β * y) - 1 - β * y * ind y) - θ * ((Real.exp (β * y) - 1) * y * ind y) := by
    intro y
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    have : Real.exp ((θ + β) * y) = Real.exp (β * y) * Real.exp (θ * y) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; unfold ind; ring
  simp_rw [hpt]
  have i1 := g_int ν hνint (θ + β) (by linarith)
  have i2 := g_int ν hνint β hβ
  have i3 := (f3_int ν hνint β hβ).const_mul θ
  have key : ∫ x in Iio 0, (Real.exp ((θ + β) * x) - 1 - (θ + β) * x * ind x -
      (Real.exp (β * x) - 1 - β * x * ind x) - θ * ((Real.exp (β * x) - 1) * x * ind x)) ∂ν =
      (∫ x in Iio 0, (Real.exp ((θ + β) * x) - 1 - (θ + β) * x * ind x) ∂ν) -
      (∫ x in Iio 0, (Real.exp (β * x) - 1 - β * x * ind x) ∂ν) -
      θ * ∫ x in Iio 0, ((Real.exp (β * x) - 1) * x * ind x) ∂ν := by
    have h := integral_sub (i1.sub i2) i3
    simp only [Pi.sub_apply] at h
    rw [h, integral_sub i1 i2, integral_const_mul]
  rw [key]
  unfold ind
  ring

end ESWAux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P L.X F)
    (beta : Real) (hBeta : 0 <= beta)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              Kyprianou.Ch03.esscherDensity L.X beta (L.ψ beta) t omega)
            omega ∂P)) :
    forall (Lbeta : AvramDividend.Classical.SpectrallyNegativeLevy Q F),
      (Lbeta.X = L.X ∧ Lbeta.σ = L.σ ∧ Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧ Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν)) ->
      forall theta : Real, -beta <= theta ->
        Lbeta.ψ theta = L.ψ (theta + beta) - L.ψ beta := by
  intro Lbeta ⟨_, hσ, hν, hc⟩ theta htheta
  unfold SpectrallyNegativeLevy.ψ
  rw [hσ, hν, hc]
  exact ESWAux.core L.c L.σ beta theta L.ν hBeta htheta L.ν_Ici L.ν_integrable
