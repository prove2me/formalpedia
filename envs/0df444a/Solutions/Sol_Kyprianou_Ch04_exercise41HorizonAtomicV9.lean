-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41HorizonAtomicV9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:34:06.108468+00:00
-- url     : https://prove2.me/submissions/f8a5183e-d281-4256-9aaa-e9ead83c0ec8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hNeg : ∀ s : NNReal, 0 < s → X s w ≤ Xleft s w)
    (hJ : Set.Countable {s : NNReal | 0 < s ∧ X s w ≠ Xleft s w})
    (t : NNReal) :
    (pathJumpMeasure X Xleft w).restrict
      (Ioc (0 : ℝ) (t : ℝ) ×ˢ Iio (0 : ℝ)) =
    Measure.sum (fun s : {s : NNReal | 0 < s ∧ s ≤ t ∧ X s w ≠ Xleft s w} =>
      Measure.dirac (((s : NNReal) : ℝ), X s w - Xleft s w)) := by
  classical
  rw [bvPathJumpMeasureAtomicV1 X Xleft w hJ]
  let J : Set NNReal := {s | 0 < s ∧ X s w ≠ Xleft s w}
  let H : Set NNReal := {s | 0 < s ∧ s ≤ t ∧ X s w ≠ Xleft s w}
  let B : Set (ℝ × ℝ) := Ioc 0 (t : ℝ) ×ˢ Iio 0
  let p : NNReal → ℝ × ℝ := fun s => ((s : ℝ), X s w - Xleft s w)
  change (Measure.sum (fun s : J => Measure.dirac (p s))).restrict B =
    Measure.sum (fun s : H => Measure.dirac (p s))
  ext A hA
  have hB : MeasurableSet B := measurableSet_Ioc.prod measurableSet_Iio
  rw [Measure.restrict_apply hA, Measure.sum_apply _ (hA.inter hB),
    Measure.sum_apply _ hA]
  rw [tsum_subtype J (fun s => Measure.dirac (p s) (A ∩ B)),
    tsum_subtype H (fun s => Measure.dirac (p s) A)]
  apply tsum_congr
  intro s
  by_cases hj : s ∈ J
  · have hm : p s ∈ B ↔ s ≤ t := by
      have hlt : X s w < Xleft s w := lt_of_le_of_ne (hNeg s hj.1) hj.2
      simp [p, B, hj.1, sub_neg.mpr hlt]
    have hh : s ∈ H ↔ s ≤ t := ⟨fun h => h.2.1, fun h => ⟨hj.1,h,hj.2⟩⟩
    simp only [Set.indicator_apply, hj, if_true, hh, Measure.dirac_apply, Set.mem_inter_iff, hm]
    by_cases ht : s ≤ t <;> simp [ht]
  · have hh : s ∉ H := fun h => hj ⟨h.1,h.2.2⟩
    simp [Set.indicator_apply, hj, hh]
