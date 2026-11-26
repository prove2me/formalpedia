-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PredictablePhysicalCountV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:30:31.226274+00:00
-- url     : https://prove2.me/submissions/6e74725f-aa35-4c6f-bf4b-d269fd11b030

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictableMarkedCountMeanV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal mOmega)
    (L : SpectrallyNegativeLevy P G)
    (T : NNReal) (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (E : Set (NNReal × Omega)) (hE : MeasurableSet[G.rightCont.predictable] E)
    (hBound : ∀ p ∈ E, p.1 ≤ T)
    (B : Set Real) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : Real)) :
    let NX : Omega → Measure (NNReal × Real) := fun w =>
      ((Measure.count.restrict {u : NNReal |
        0 < u ∧ L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u : NNReal => (u, L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    (∫⁻ w, NX w {p : NNReal × Real | (p.1,w) ∈ E ∧ p.2 ∈ B} ∂P) =
      (((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E) *
        L.ν B := by
  exact Kyprianou.Ch04.exercise46PredictableMarkedCountMeanV1
    P G L T E hE hBound B hB hNeg
