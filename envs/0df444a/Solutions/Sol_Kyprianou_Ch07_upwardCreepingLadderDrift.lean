-- Prove2me | solution 1 for Kyprianou.Ch07.upwardCreepingLadderDrift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:58:55.563267+00:00
-- url     : https://prove2.me/submissions/49fc6c90-419d-4cb6-833d-daa4bc59c4c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_creepingImpliesPositiveAscendingDrift
import Theorems.Thm_Kyprianou_Ch07_positiveAscendingDriftImpliesCreeping
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (L : NNReal → Omega → NNReal)
    (kappa : Complex → Complex → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hL : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X L)
    (hKappa : ∀ (a b : Complex),
      0 ≤ a.re → 0 ≤ b.re → ∀ t : NNReal,
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime L t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (-a * (↑((tau.untopD 0 : NNReal) : Real) : Complex) -
            b * (↑(Kyprianou.Ch06.runningMaximum X
                (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) * kappa a b)) :
    ∀ x : Real, 0 < x →
      ((0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) x) ↔
        ∃ d : Real, 0 < d ∧
          Tendsto (fun beta : Real =>
            (kappa 0 (beta : Complex)).re / beta)
            atTop (nhds d)) := by
  intro x hx
  constructor
  · intro hCreep
    exact Kyprianou.Ch07.creepingImpliesPositiveAscendingDrift
      P X F L kappa hX hNonCompound hL hKappa x hx hCreep
  · intro hDrift
    exact Kyprianou.Ch07.positiveAscendingDriftImpliesCreeping
      P X F L kappa hX hNonCompound hL hKappa x hx hDrift
