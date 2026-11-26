-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPassageFinite_nullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:19:24.173843+00:00
-- url     : https://prove2.me/submissions/8cff47ce-7449-4a41-86fc-e6c1755afef1

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Theorems.Thm_Kyprianou_Ch05_unkilledPassageFinite_iff_nat
import Theorems.Thm_Kyprianou_Ch05_levyCoordinateMeasurableCompletion
import Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0) (x : Real) :
    NullMeasurableSet {w : Omega | PassageFinite Y death x w} P := by
  let A (n : ℕ) := {w : Omega | 0 < n ∧ x < Y (n : NNReal) w}
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    have hc : NullMeasurable (Y (n : NNReal)) P :=
      levyCoordinateMeasurableCompletion P Y hKilled.1.1 (n : NNReal)
    exact (NullMeasurableSet.const (0 < n)).inter (hc measurableSet_Ioi)
  apply (NullMeasurableSet.iUnion hA).congr
  filter_upwards [hKilled.1.2] with w hw
  change (w ∈ ⋃ n, A n) = PassageFinite Y death x w
  apply propext
  simpa only [Set.mem_iUnion, A, Set.mem_setOf_eq] using
    (unkilledPassageFinite_iff_nat Y death (hKilled.2.2.2.1 rfl) x w hw).symm
