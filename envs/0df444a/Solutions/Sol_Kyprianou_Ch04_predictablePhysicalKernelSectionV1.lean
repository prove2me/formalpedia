-- Prove2me | solution 1 for Kyprianou.Ch04.predictablePhysicalKernelSectionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:31:23.513777+00:00
-- url     : https://prove2.me/submissions/acff7ee0-57b2-45ca-aaf3-fa22592fb227

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Each physical time-mark section of a marked predictable kernel is measurable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g) (ω : Ω) :
    Measurable (fun z : ℝ × ℝ => g ((z.1.toNNReal,ω),z.2)) := by
  have hq : Measurable (fun z : ℝ × ℝ => ((z.1.toNNReal,ω),z.2)) :=
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_const).prodMk
      measurable_snd
  exact (hg.mono (Kyprianou.Ch04.markedPredictableLeAmbientProduct F) le_rfl).comp hq
