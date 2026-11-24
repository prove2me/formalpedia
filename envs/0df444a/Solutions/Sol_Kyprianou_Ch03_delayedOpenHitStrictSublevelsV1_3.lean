-- Prove2me | solution 3 for Kyprianou.Ch03.delayedOpenHitStrictSublevelsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:31:23.479721+00:00
-- url     : https://prove2.me/submissions/e75662ae-c1ff-44c5-b931-bc58b8996f18

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAEModV1
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitRationalEventMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitRationalWitnessV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (a : NNReal) (B : Set ℝ) (hB : IsOpen B) (s : NNReal) :
    MeasurableSet[F s] {w | sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) < (s : WithTop NNReal)} := by
  let U : Set Omega := ⋃ q : ℚ, ⋃ (_ : a ≤ Real.toNNReal q ∧ Real.toNNReal q < s),
    {w | X (Real.toNNReal q) w ∈ B}
  apply Kyprianou.Ch03.completedNaturalMeasurableAEModV1 P F X hNatural s _ U
    (Kyprianou.Ch03.delayedOpenHitRationalEventMeasurableV1 P F X hNatural a s B hB)
  filter_upwards [hX.cadlag_ae] with w hw
  simp only [U, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [Kyprianou.Ch03.delayedOpenHitRationalWitnessV1 X B hB a w (fun t => (hw t).1) s]
  tauto
