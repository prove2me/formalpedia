-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ZeroVisitCounterCadlag
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:53:18.679877+00:00
-- url     : https://prove2.me/submissions/1a32fbbb-da1e-4fec-9908-48d723737853
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitsLocallyFiniteV1
import Theorems.Thm_Kyprianou_Ch04_exercise41LocallyFiniteZeroCountCadlagV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Local finiteness of positive zero visits and the deterministic locally finite counting theorem give the two cadlag conditions. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    ∀ᵐ omega : Omega ∂P,
      (∀ t : NNReal,
        Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0}) ∧
      (∀ t : NNReal,
        ContinuousWithinAt
          (fun u : NNReal =>
            (({s : NNReal | 0 < s ∧ s ≤ u ∧ L.X s omega = 0}).ncard : Real))
          (Set.Ici t) t) ∧
      (∀ t : NNReal, 0 < t →
        ∃ l : Real,
          Tendsto
            (fun u : NNReal =>
              (({s : NNReal | 0 < s ∧ s ≤ u ∧ L.X s omega = 0}).ncard : Real))
            (nhdsWithin t (Set.Iio t)) (nhds l)) := by
  filter_upwards [Kyprianou.Ch04.exercise41ZeroVisitsLocallyFiniteV1
    P F L hBV hd] with omega hfinite
  refine ⟨hfinite, ?_⟩
  let Z : Set NNReal := {s | 0 < s ∧ L.X s omega = 0}
  have hEq (t : NNReal) : Z ∩ Set.Iic t =
      {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0} := by
    ext s
    simp only [Z, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic]
    tauto
  have hFin (t : NNReal) : (Z ∩ Set.Iic t).Finite := hEq t ▸ hfinite t
  simpa only [hEq] using Kyprianou.Ch04.exercise41LocallyFiniteZeroCountCadlagV1 Z hFin
