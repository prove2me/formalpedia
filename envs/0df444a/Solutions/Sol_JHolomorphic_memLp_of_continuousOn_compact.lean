-- Prove2me | solution 1 for JHolomorphic.memLp_of_continuousOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:36:21.134744+00:00
-- url     : https://prove2.me/submissions/86008e9a-e97c-499d-88c5-cc21fa2050a5

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- `L^p` on a compact set is preserved by applying a continuous operator family. -/
theorem memLp_clm_apply_of_continuousOn_aux {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {K : Set ℂ} (hK : IsCompact K) {p : ℝ≥0∞}
    {B : ℂ → X →L[ℝ] Y} (hB : ContinuousOn B K) {r : ℂ → X}
    (hr : MemLp r p (volume.restrict K)) : MemLp (fun z => B z (r z)) p (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hB
  have hBm : AEStronglyMeasurable B (volume.restrict K) :=
    hB.aestronglyMeasurable hK.measurableSet
  have hm : AEStronglyMeasurable (fun z => B z (r z)) (volume.restrict K) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hBm.prodMk hr.1)
  refine hr.of_le_mul (c := C) hm ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact (B z).le_of_opNorm_le (hC z hz) _

/-- A continuous map is in `L^p` on a compact set. -/
theorem memLp_of_continuousOn_compact_aux {X : Type*} [NormedAddCommGroup X] {K : Set ℂ}
    (hK : IsCompact K) {p : ℝ≥0∞} {f : ℂ → X} (hf : ContinuousOn f K) :
    MemLp f p (volume.restrict K) := by
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine MemLp.of_bound (hf.aestronglyMeasurable hK.measurableSet) C ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hC z hz

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution {X : Type*} [NormedAddCommGroup X] {K : Set ℂ}
    (hK : IsCompact K) {p : ℝ≥0∞} {f : ℂ → X} (hf : ContinuousOn f K) :
    MemLp f p (volume.restrict K) :=
  memLp_of_continuousOn_compact_aux hK hf
