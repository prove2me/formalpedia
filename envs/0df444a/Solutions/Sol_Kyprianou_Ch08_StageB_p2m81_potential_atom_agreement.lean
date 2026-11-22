-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_potential_atom_agreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T01:40:54.43445+00:00
-- url     : https://prove2.me/submissions/58f08700-7a82-4561-bb78-2b52f66c678e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
import Theorems.Thm_AvramDividend_Classical_withDensity_injective_of_everywhere_pos_finite

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

lemma p2m81_e_meas : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-1 * y))) :=
  Measurable.ennreal_ofReal (by fun_prop)

lemma p2m81_tilt (f : ℝ → ℝ) (ν : Measure ℝ)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s))
    (t : ℝ) (ht : t < 1) :
    (∫⁻ a, ENNReal.ofReal (Real.exp (t * a)) ∂(ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y)))) = ENNReal.ofReal ((1 - t) / f (1 - t)) := by
  have hgE : Measurable (fun a : ℝ => ENNReal.ofReal (Real.exp (t * a))) := Measurable.ennreal_ofReal (by fun_prop)
  have hwd := lintegral_withDensity_eq_lintegral_mul ν p2m81_e_meas hgE
  refine hwd.trans ?_
  have hcongr : ((fun y => ENNReal.ofReal (Real.exp (-1 * y))) * fun a => ENNReal.ofReal (Real.exp (t * a))) = fun a => ENNReal.ofReal (Real.exp (-(1 - t) * a)) := by
    funext a; simp only [Pi.mul_apply]; rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply congrArg ENNReal.ofReal; apply congrArg Real.exp; ring
  rw [hcongr]; exact hlap (1 - t) (by linarith)

lemma p2m81_finite (f : ℝ → ℝ) (ν : Measure ℝ)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s)) :
    IsFiniteMeasure (ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) := by
  refine isFiniteMeasure_withDensity ?_
  show (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂ν) ≠ ∞
  rw [hlap 1 one_pos]; exact ENNReal.ofReal_ne_top

lemma p2m81_mgf (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s) (ν : Measure ℝ)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s))
    (t : ℝ) (ht : t < 1) :
    ProbabilityTheory.mgf id (ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) t = (1 - t) / f (1 - t) := by
  simp only [ProbabilityTheory.mgf, id]
  have h1 := integral_eq_lintegral_of_nonneg_ae (μ := ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) (f := fun x : ℝ => Real.exp (t * x)) (ae_of_all _ fun x => (Real.exp_pos _).le) (Measurable.aestronglyMeasurable (by fun_prop))
  refine h1.trans ?_
  show ENNReal.toReal (∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (t * a)) ∂(ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y)))) = (1 - t) / f (1 - t)
  rw [p2m81_tilt f ν hlap t ht, ENNReal.toReal_ofReal (div_nonneg (by linarith) (le_of_lt (hpos (1 - t) (by linarith))))]

lemma p2m81_mem (f : ℝ → ℝ) (ν : Measure ℝ)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s))
    (t : ℝ) (ht : t < 1) :
    t ∈ ProbabilityTheory.integrableExpSet id (ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) := by
  have hne : (∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (t * a)) ∂(ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y)))) ≠ ∞ := by
    rw [p2m81_tilt f ν hlap t ht]; exact ENNReal.ofReal_ne_top
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) (f := fun x : ℝ => Real.exp (t * x)) (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun x => (Real.exp_pos _).le)).mp hne

lemma p2m81_analytic (f : ℝ → ℝ) (ν : Measure ℝ)
    (hlap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s)) :
    AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id (ν.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y)))) {z : ℂ | z.re < 1} := by
  refine ProbabilityTheory.analyticOnNhd_complexMGF.mono ?_; intro z hz
  exact isOpen_Iio.subset_interior_iff.mpr (fun t ht => p2m81_mem f ν hlap t ht) hz

theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (ν1 ν2 : Measure ℝ)
    (h1supp : ν1 (Iio (0 : ℝ)) = 0)
    (h2supp : ν2 (Iio (0 : ℝ)) = 0)
    (h1lap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν1) = ENNReal.ofReal (s / f s))
    (h2lap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν2) = ENNReal.ofReal (s / f s))
    (x : ℝ) (hx : 0 < x) : ν1 {x} = ν2 {x} := by
  haveI hfin1 := p2m81_finite f ν1 h1lap; haveI hfin2 := p2m81_finite f ν2 h2lap
  have hreal : ∀ t : ℝ, t < 1 → ProbabilityTheory.complexMGF id (ν1.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) (t : ℂ) = ProbabilityTheory.complexMGF id (ν2.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) (t : ℂ) := by
    intro t ht; rw [ProbabilityTheory.complexMGF_ofReal, ProbabilityTheory.complexMGF_ofReal]; congr 1
    exact (p2m81_mgf f hpos ν1 h1lap t ht).trans (p2m81_mgf f hpos ν2 h2lap t ht).symm
  have htilt := AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Iio (ν1.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) (ν2.withDensity fun y => ENNReal.ofReal (Real.exp (-1 * y))) 1 one_pos (p2m81_analytic f ν1 h1lap) (p2m81_analytic f ν2 h2lap) hreal
  have hν : ν1 = ν2 := AvramDividend.Classical.withDensity_injective_of_everywhere_pos_finite ν1 ν2 (fun y => ENNReal.ofReal (Real.exp (-1 * y))) p2m81_e_meas (fun y => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne') (fun y => ENNReal.ofReal_ne_top) htilt
  rw [hν]
