-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDyadicPairsAEMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:49:33.837229+00:00
-- url     : https://prove2.me/submissions/929d68a5-0656-4c7c-a6d4-6d2e063c7752

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (n : ℕ) :
    AEMeasurable (fun ω : Omega =>
      let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))
      (a, a - X t ω)) P ∧
    AEMeasurable (fun ω : Omega =>
      let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))
      (X t ω - b, -b)) P := by
  have hc := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  let V (i : Fin (2 ^ n + 1)) (ω : Omega) :=
    X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω
  have ha : AEMeasurable (fun ω => sSup (Set.range (fun i => V i ω))) P :=
    AEMeasurable.iSup fun i => hc _
  have hb : AEMeasurable (fun ω => sInf (Set.range (fun i => V i ω))) P :=
    AEMeasurable.iInf fun i => hc _
  exact ⟨ha.prodMk (ha.sub (hc t)), ((hc t).sub hb).prodMk hb.neg⟩
