-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_f_closed_form_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:16:35.182927+00:00
-- url     : https://prove2.me/submissions/b20b82d1-f258-4729-ba3d-3f8586d71cf9

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_excess_laplace_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d))
    (s : ℝ) (hs : 0 < s) (hne : s ≠ d) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s))) := by
  haveI := hprob
  have hd_ne : d ≠ 0 := ne_of_gt hd
  have hcompl : (Iio (0 : ℝ))ᶜ = Ici (0 : ℝ) := compl_Iio
  have hae_mem : Ici (0 : ℝ) ∈ ae ρ := hcompl ▸ compl_mem_ae_iff.mpr hsupp
  have hae_nonneg : ∀ᵐ y ∂ρ, 0 ≤ y :=
    Filter.eventually_of_mem hae_mem fun y hy => mem_Ici.mp hy
  have hLle : ∀ t : ℝ, 0 < t → (∫⁻ y, ENNReal.ofReal (Real.exp (-t * y)) ∂ρ) ≤ 1 := by
    intro t ht
    have hae : ∀ᵐ y ∂ρ, ENNReal.ofReal (Real.exp (-t * y)) ≤ 1 := by
      filter_upwards [hae_nonneg] with y hy
      have harg : -t * y ≤ 0 := by have := mul_nonneg ht.le hy; linarith
      have hexp : Real.exp (-t * y) ≤ 1 := Real.exp_le_one_iff.mpr harg
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hexp
    have h := lintegral_mono_ae hae
    rwa [lintegral_one, IsProbabilityMeasure.measure_univ] at h
  have hLne_s := ne_top_of_le_ne_top (by simp) (hLle s hs)
  have hEq1 := Kyprianou.Ch08.StageB.p2m81_tail_kernel_excess_laplace_public d ρ hprob hsupp s hs
  set r : ℝ := (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal with hr
  have hrNN : 0 ≤ r := ENNReal.toReal_nonneg
  have hLρ_eq : (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) = ENNReal.ofReal r :=
    (ENNReal.ofReal_toReal hLne_s).symm
  have hfd_ne : f d - f s ≠ 0 := by
    intro h0
    have hfd_pos : 0 < f d := hpos d hd
    have hsd : s / d ≠ 1 := by
      intro h
      exact hne ((div_eq_one_iff_eq hd_ne).mp h)
    have hRHS_ne : f d * (1 - s / d) ≠ 0 :=
      mul_ne_zero (ne_of_gt hfd_pos) (sub_ne_zero.mpr (Ne.symm hsd))
    have heq_s := heq s hs
    rw [h0, zero_mul] at heq_s
    exact hRHS_ne heq_s.symm
  have heq_s : (f d - f s) * r = f d * (1 - s / d) := heq s hs
  have heq_cleared : ((f d - f s) * r) * d = f d * (d - s) := by
    have hmul : (f d * (1 - s / d)) * d = f d * (d - s) := by
      field_simp
    calc ((f d - f s) * r) * d
        = (f d * (1 - s / d)) * d := by rw [heq_s]
      _ = f d * (d - s) := hmul
  have hRealEq : d * (1 - r) / s = (s * f d - d * f s) / (s * (f d - f s)) := by
    have hs_ne : s ≠ 0 := ne_of_gt hs
    field_simp
    linear_combination -heq_cleared
  have h1sub : (1 - ENNReal.ofReal r) = ENNReal.ofReal (1 - r) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hrNN]
  rw [hEq1, hLρ_eq, h1sub, ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_div_of_pos hs, hRealEq]
