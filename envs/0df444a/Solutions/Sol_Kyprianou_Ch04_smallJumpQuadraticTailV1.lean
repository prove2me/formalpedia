-- Prove2me | solution 1 for Kyprianou.Ch04.smallJumpQuadraticTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:06:48.582809+00:00
-- url     : https://prove2.me/submissions/d408e421-49b2-4580-9157-6691a6ba2531

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false
/-- Vanishing two-sided small-jump quadratic tails. -/
theorem solution
    (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hSub : ∀ n, B n ⊆ Ioo (-1 : ℝ) 1)
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ)) :
    Tendsto (fun n => ∫⁻ z in B n, ENNReal.ofReal (z ^ 2) ∂ν)
      atTop (𝓝 0) := by
  let μ := (ν.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun z : ℝ => ENNReal.ofReal (z ^ 2))
  have hμ : ∀ n, μ (B n) = ∫⁻ z in B n, ENNReal.ofReal (z ^ 2) ∂ν := by
    intro n
    rw [MeasureTheory.withDensity_apply _ (hB n), Measure.restrict_restrict (hB n)]
    rw [inter_eq_left.mpr (hSub n)]
  have hfin : μ (B 0) ≠ ⊤ := by
    rw [hμ]
    apply ne_of_lt
    have heq : (∫⁻ z in B 0, ENNReal.ofReal (z ^ 2) ∂ν) =
        ∫⁻ z in B 0, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hB 0)] with z hz
      have hh := hSub 0 hz
      rw [Set.mem_Ioo] at hh
      rw [min_eq_right]
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.2.le) (by linarith : 0 ≤ z + 1)]
    rw [heq]
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hν.2
  have hz : μ ({0} : Set ℝ) = 0 := by
    rw [MeasureTheory.withDensity_apply _ (measurableSet_singleton _)]
    rw [Measure.restrict_restrict (measurableSet_singleton _)]
    have hzero : ν (({0} : Set ℝ) ∩ Ioo (-1 : ℝ) 1) = 0 :=
      measure_mono_null inter_subset_left hν.1
    rw [Measure.restrict_eq_zero.mpr hzero]
    simp
  have hi : μ (⋂ n, B n) = 0 := measure_mono_null hInter hz
  have ht := MeasureTheory.tendsto_measure_iInter_atTop
    (fun n => (hB n).nullMeasurableSet) hAnti ⟨0, hfin⟩
  rw [hi] at ht
  change Tendsto (fun n => μ (B n)) atTop (𝓝 0) at ht
  simpa only [hμ] using ht
