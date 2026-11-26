-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46DeterministicRestrictedPathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:59:51.107809+00:00
-- url     : https://prove2.me/submissions/24957b63-5bc9-42dc-b7db-cf33bce64b26

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (s : NNReal) (B : Set Omega) (hB : MeasurableSet[F s] B) :
    Measure.map (fun w u => L.X (s + u) w - L.X s w) (P.restrict B) =
      P B • Measure.map (fun w u => L.X u w) P := by
  have hstop : IsStoppingTime F (fun _ : Omega => (s : WithTop NNReal)) := by
    intro t
    by_cases h : s ≤ t <;> simp [h]
  apply levy_finiteStopping_restrictedFuturePath_mapLaw L (fun _ => s) hstop B
  intro t
  by_cases h : s ≤ t
  · simpa [h] using F.mono h _ hB
  · simp [h]
