-- Prove2me | solution 1 for Kyprianou.Ch02.markedFibreIntegralBoundFromEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:59:00.386426+00:00
-- url     : https://prove2.me/submissions/2921dd8b-ffb7-484b-8fad-04d33227fc83

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (c : ℝ) (hc : 0 ≤ c)
    (henvelope : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hfibre : μ ({(t : ℝ)} ×ˢ B) ≤ 1) :
    |∫ z in ({(t : ℝ)} ×ˢ B), z.2 ∂μ| ≤ c  := by
  let D : Set (ℝ × ℝ) := {(t : ℝ)} ×ˢ B
  let E : Set (ℝ × ℝ) := {z | ¬ ‖z.2‖ ≤ c}
  have hEm : MeasurableSet E :=
    (measurableSet_le continuous_snd.norm.measurable measurable_const).compl
  have hmass : (μ.restrict D) Set.univ ≤ 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hfibre
  letI : IsFiniteMeasure (μ.restrict D) := ⟨lt_of_le_of_lt hmass (by simp)⟩
  have hBad : (μ.restrict D) E = 0 := by
    rw [Measure.restrict_apply hEm]
    refine measure_mono_null ?_ henvelope
    intro z hz
    have hzt : z.1 = (t : ℝ) := Set.mem_singleton_iff.mp hz.2.1
    have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have htT' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
    refine ⟨⟨by rw [hzt]; exact ht0, by rw [hzt]; exact htT'⟩, ⟨?_, hsmall hz.2.2⟩⟩
    exact lt_of_not_ge (by simpa only [E, Set.mem_setOf_eq, Real.norm_eq_abs] using hz.1)
  have hbound : ∀ᵐ z ∂μ.restrict D, ‖z.2‖ ≤ c := ae_iff.2 hBad
  have hreal : (μ.restrict D).real Set.univ ≤ 1 := by
    change ((μ.restrict D) Set.univ).toReal ≤ 1
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmass
  change |∫ z, z.2 ∂μ.restrict D| ≤ c
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const hbound).trans ?_
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hreal hc
