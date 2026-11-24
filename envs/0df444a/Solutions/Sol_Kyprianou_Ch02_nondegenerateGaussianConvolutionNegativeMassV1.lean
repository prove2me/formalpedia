-- Prove2me | solution 1 for Kyprianou.Ch02.nondegenerateGaussianConvolutionNegativeMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:24:07.159883+00:00
-- url     : https://prove2.me/submissions/23dfad09-f2b4-4704-911b-50bbecc71bb4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (v : ℝ≥0) (hv : 0 < v) :
    0 < (Q ∗ gaussianReal 0 v) (Iio (0 : ℝ)) := by
  have hpos : ∃ n : ℕ, 0 < Q (Iic (n : ℝ)) := by
    by_contra! h
    have hu : (⋃ n : ℕ, Iic (n : ℝ)) = univ := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hn⟩
    have hz : Q (⋃ n : ℕ, Iic (n : ℝ)) = 0 :=
      measure_iUnion_null fun n => le_antisymm (h n) bot_le
    rw [hu, measure_univ] at hz
    exact one_ne_zero hz
  obtain ⟨n, hn⟩ := hpos
  have hg : 0 < gaussianReal 0 v (Iio (-(n : ℝ))) := by
    by_contra! h
    have hz : gaussianReal 0 v (Iio (-(n : ℝ))) = 0 := le_antisymm h bot_le
    have hvz := gaussianReal_absolutelyContinuous' 0 hv.ne' hz
    have hp : 0 < volume (Iio (-(n : ℝ))) := Measure.measure_Iio_pos volume _
    exact hp.ne' hvz
  change 0 < (Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
    (Q.prod (gaussianReal 0 v))) (Iio 0)
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [Measure.map_apply hm measurableSet_Iio]
  have hsub : Iic (n : ℝ) ×ˢ Iio (-(n : ℝ)) ⊆
      (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio 0 := by
    intro p hp
    change p.1 + p.2 < 0
    have h1 : p.1 ≤ (n : ℝ) := hp.1
    have h2 : p.2 < -(n : ℝ) := hp.2
    linarith
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos hn.ne' hg.ne'
