-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RightContPhysicalMarkedKernelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:48.41181+00:00
-- url     : https://prove2.me/submissions/4801db5e-cdf1-445c-bf6c-bfc0c1a639ed

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    let NX : Omega → Measure (NNReal × Real) := fun w =>
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
        Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    let K : Omega → @Measure ((NNReal × Omega) × Real)
      (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
        (inferInstance : MeasurableSpace Real)) := fun w =>
      @Measure.map (NNReal × Real) ((NNReal × Omega) × Real) inferInstance
        (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
          (inferInstance : MeasurableSpace Real)) (fun p => ((p.1,w),p.2)) (NX w)
    AEMeasurable K P := by
  dsimp only
  obtain ⟨Y,hY,_,_,_⟩ := avram_wave5_04_source_rightCont_levy_lift L
  exact avram_wave5_02a_full_original_kernel_measurable Y _ (by intro w; simp only [hY])
