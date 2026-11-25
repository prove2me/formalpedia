-- Prove2me | solution 1 for Kyprianou.Ch04.expProductClockTerminalChar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T09:49:48.473172+00:00
-- url     : https://prove2.me/submissions/26065e37-c8bc-4d7d-99f4-f933c37f9a67

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_expMeasureComplexTransform
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (Psi : ℝ → ℂ)
    (hPsi : ∀ (t : NNReal) (theta : ℝ),
      (∫ ω, Complex.exp (Complex.I * (theta : ℂ) * (L.X t ω : ℂ)) ∂P) =
        Complex.exp (-((t : ℝ) : ℂ) * Psi theta))
    (q : ℝ) (hq : 0 < q) (a : ℝ) :
    (∫ z : Ω × ℝ, Complex.exp (Complex.I * (a : ℂ) *
      (L.X z.2.toNNReal z.1 : ℂ)) ∂(P.prod (expMeasure q))) =
      (q : ℂ) / (Psi a + (q : ℂ)) := by
  letI : IsProbabilityMeasure P := L.isProbability
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  have hnorm (x : ℝ) : ‖Complex.exp (Complex.I * (a : ℂ) * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hnonneg : 0 ≤ (Psi a).re := by
    have h := norm_integral_le_integral_norm (μ := P)
      (fun ω => Complex.exp (Complex.I * (a : ℂ) * (L.X 1 ω : ℂ)))
    simp_rw [hnorm] at h
    rw [hPsi 1 a, Complex.norm_exp] at h
    simpa [Complex.mul_re] using h
  have hm := levy_exponential_real_clock_extrema_drawdown_measurable L
  have hX : Measurable (fun z : Ω × ℝ => L.X z.2.toNNReal z.1) := by
    convert hm.fst.fst.sub hm.snd using 1
    ext z
    change L.X z.2.toNNReal z.1 = runningSup L z.2.toNNReal z.1 -
      (runningSup L z.2.toNNReal z.1 - L.X z.2.toNNReal z.1)
    ring
  have hfun : Measurable (fun z : Ω × ℝ =>
      Complex.exp (Complex.I * (a : ℂ) * (L.X z.2.toNNReal z.1 : ℂ))) := by
    fun_prop
  rw [integral_prod_symm _ (Integrable.of_bound hfun.aestronglyMeasurable 1
    (ae_of_all _ (fun z => (hnorm _).le)))]
  simp_rw [hPsi]
  have hs : ∀ᵐ t : ℝ ∂expMeasure q, 0 ≤ t := by
    have ht := avram_ws01e_b_expMeasure_strict_survival_real q 0 hq le_rfl
    have hpos : expMeasure q (Ioi 0) = 1 := by simpa using ht
    have hAE : ∀ᵐ t : ℝ ∂expMeasure q, t ∈ Ioi (0 : ℝ) :=
      by
        rw [ae_iff]
        change expMeasure q (Ioi (0 : ℝ))ᶜ = 0
        rw [measure_compl measurableSet_Ioi (measure_ne_top _ _), hpos]
        simp
    filter_upwards [hAE] with t ht
    exact ht.le
  calc
    _ = ∫ t : ℝ, Complex.exp ((-Psi a) * (t : ℂ)) ∂expMeasure q := by
      apply integral_congr_ae
      filter_upwards [hs] with t ht
      rw [Real.coe_toNNReal _ ht]
      congr 1
      ring
    _ = _ := by
      rw [Kyprianou.Ch04.expMeasureComplexTransform q hq (-Psi a) (by
        simp only [Complex.neg_re]; linarith)]
      congr 1
      ring
