-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionFutureSupProxyAEV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:08.101241+00:00
-- url     : https://prove2.me/submissions/e2898071-2196-43b9-8138-e9221d1f937b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedFutureSupVersionV1
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (r : Omega → NNReal) (c : ℝ) (t : NNReal) :
    ∃ K : (NNReal → ℝ) → ℝ, Measurable K ∧
      (∀ᵐ w ∂P,
        K (fun u => X u w) = LevyExtrema.SBA.runSup (fun u => c * X u w) t) ∧
      (∀ᵐ w ∂P,
        K (fun u => X (r w + u) w - X (r w) w) =
          LevyExtrema.SBA.runSup (fun u => c * (X (r w + u) w - X (r w) w)) t) := by
  exact reflectedSignedFutureSupVersionV1 P X hX c r t
