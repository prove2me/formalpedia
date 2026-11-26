-- Prove2me | solution 1 for Kyprianou.Ch05.isLevyProcess_completion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:07:32.296602+00:00
-- url     : https://prove2.me/submissions/62c63435-25cb-4e3e-bf20-cb4705ef7884

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_completionMapEqOfAEMeasurable
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (Y : NNReal → Omega → Real)
    (hY : ProbabilityTheory.IsLevyProcess Y P) :
    ProbabilityTheory.IsLevyProcess
      (fun t (w : NullMeasurableSpace Omega P) => Y t w) P.completion := by
  constructor
  · exact hY.start_zero
  · intro n t ht
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hs
    exact (iIndepFun_iff_measure_inter_preimage_eq_mul.mp
      (hY.indep_increments n t ht)) S hs
  · intro s t
    have h := hY.stationary_increments s t
    refine ⟨h.aemeasurable_fst.nullMeasurable.measurable'.aemeasurable,
      h.aemeasurable_snd.nullMeasurable.measurable'.aemeasurable, ?_⟩
    exact (Kyprianou.Ch05.completionMapEqOfAEMeasurable P _
      h.aemeasurable_fst).trans (h.map_eq.trans
        (Kyprianou.Ch05.completionMapEqOfAEMeasurable P _
          h.aemeasurable_snd).symm)
  · exact hY.cadlag_ae
