-- Prove2me | solution 1 for Kyprianou.Ch03.closedHitDelayedApproxAEEqV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:03:08.826057+00:00
-- url     : https://prove2.me/submissions/89583d11-73d1-4f0f-acf9-3e347d6aeebd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxV1
import Theorems.Thm_Kyprianou_Ch03_positiveHitInfDelayedClosedV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (B : Set ℝ) (hB : IsClosed B)
    (hStop : ∀ j n : ℕ, IsStoppingTime F (fun w => sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧
        X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}))) :
    ∀ᵐ w ∂P, Kyprianou.Ch03.firstHittingTime X B w =
      ⨅ j : ℕ, ⨆ n : ℕ, sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧
        X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}) := by
  let T (j n : ℕ) (w : Omega) : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧
        X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B})
  have h (j : ℕ) := Kyprianou.Ch03.delayedClosedHitFixedApproxV1 P F X hX hNatural B hB
    (1 / ((j : NNReal) + 1)) (T j) (fun _ _ => rfl) (hStop j)
  rw [← ae_all_iff] at h
  filter_upwards [h] with w hw
  rw [Kyprianou.Ch03.positiveHitInfDelayedClosedV1 X B w]
  exact congrArg iInf (funext fun j => (hw j).symm)
