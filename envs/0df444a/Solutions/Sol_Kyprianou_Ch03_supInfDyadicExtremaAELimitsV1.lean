-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDyadicExtremaAELimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:48:33.392867+00:00
-- url     : https://prove2.me/submissions/39c6b70b-da9a-4280-bd1e-b95a7e8124ae

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_supInfCadlagDyadicExtremaLimitsV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))) atTop
        (𝓝 (LevyExtrema.SBA.runSup (fun s => X s ω) t)) ∧
      Tendsto (fun n : ℕ => sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))) atTop
        (𝓝 (sInf ((fun s : NNReal => X s ω) '' Set.Icc 0 t))) := by
  filter_upwards [hX.cadlag_ae] with ω hω
  exact Kyprianou.Ch03.supInfCadlagDyadicExtremaLimitsV1 (fun s => X s ω) hω t ht
