-- Prove2me | solution 1 for Kyprianou.Ch01.integratedTailLaw_exists
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:26:45.756815+00:00
-- url     : https://prove2.me/submissions/de8dc719-7f73-4e46-88f2-53eb3e917686

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem solution
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu) :
    ∃ eta : Measure ℝ, IsProbabilityMeasure eta ∧
      eta (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ x : ℝ, 0 ≤ x →
        (eta (Set.Iic x)).toReal = integratedTailCDF F mu x := by
  set g : ℝ → ℝ := fun y => (1 / mu) * (F (Set.Ioi y)).toReal with hg
  have hanti : Antitone (fun y : ℝ => (F (Set.Ioi y)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hab))
  have hmeasT : Measurable (fun y : ℝ => (F (Set.Ioi y)).toReal) := hanti.measurable
  have hgmeas : Measurable g := measurable_const.mul hmeasT
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y =>
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  refine ⟨(volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y => ENNReal.ofReal (g y)),
    ?_, ?_, ?_⟩
  · -- total mass via the layer-cake formula
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hpos : ∀ᵐ x ∂F, 0 ≤ x := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} ⊆ Set.Iic 0 := fun a ha => by
        simp only [Set.mem_ofPred_eq, not_le] at ha; exact le_of_lt ha
      exact measure_mono_null this hclaimpos
    have hlayer := MeasureTheory.lintegral_eq_lintegral_meas_lt F hpos
      (measurable_id.aemeasurable)
    have hint_eq : ∫⁻ x, ENNReal.ofReal x ∂F = ENNReal.ofReal mu := by
      rw [← hmean, ofReal_integral_eq_lintegral_ofReal hclaimint hpos]
    have hlay2 : ∫⁻ t in Set.Ioi (0:ℝ), F (Set.Ioi t) = ENNReal.ofReal mu := by
      rw [← hint_eq, hlayer]; rfl
    have : (fun y => ENNReal.ofReal (g y)) =
        fun y => ENNReal.ofReal (1 / mu) * F (Set.Ioi y) := by
      funext y
      simp only [hg]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hantiE : Antitone (fun y : ℝ => F (Set.Ioi y)) := fun a b hab =>
      measure_mono (Set.Ioi_subset_Ioi hab)
    rw [this, lintegral_const_mul _ hantiE.measurable, hlay2,
      ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hmu.ne',
      ENNReal.ofReal_one]
  · rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have : Set.Iio (0:ℝ) ∩ Set.Ioi 0 = ∅ := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_and, not_lt]; intro h; exact h.le
    rw [this, Measure.restrict_empty, lintegral_zero_measure]
  · intro x hx
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Set.Iic x ∩ Set.Ioi (0:ℝ) = Set.Ioc 0 x := by
      ext a; simp [and_comm]
    rw [hset]
    have hgint : Integrable g (volume.restrict (Set.Ioc (0:ℝ) x)) := by
      refine Integrable.of_bound (C := 1 / mu) hgmeas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_of_nonneg (hg_nonneg y)]
      have h1 : (F (Set.Ioi y)).toReal ≤ 1 := by
        have := prob_le_one (μ := F) (s := Set.Ioi y)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      have : 0 ≤ 1 / mu := by positivity
      simpa [hg] using mul_le_of_le_one_right this h1
    rw [← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall hg_nonneg),
      ENNReal.toReal_ofReal (integral_nonneg hg_nonneg)]
    simp only [hg, integratedTailCDF]
    rw [integral_const_mul]
