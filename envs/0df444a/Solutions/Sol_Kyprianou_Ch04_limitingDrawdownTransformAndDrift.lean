-- Prove2me | solution 1 for Kyprianou.Ch04.limitingDrawdownTransformAndDrift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:04:19.386984+00:00
-- url     : https://prove2.me/submissions/8d686812-64a2-44c1-a575-42123471c2ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_LaplaceTransform
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_nonpositiveMeanClassification
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_positiveMeanClassification
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Corollary 4.9 (p. 100): limiting transform of running supremum minus X, and drift classification. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) :
    let nonnegativeSlope : Real :=
      max 0 (sInf ((fun theta : Real => L.ψ theta / theta) '' Set.Ioi 0))
    let meanNonpositive : Prop :=
      forall epsilon : Real, 0 < epsilon ->
        exists theta : Real, 0 < theta ∧ L.ψ theta < epsilon * theta
    (∀ beta : Real, 0 < beta →
      Tendsto
        (fun t : NNReal =>
          ∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t) - L.X t omega)) ∂P)
        atTop (nhds (nonnegativeSlope * beta / L.ψ beta))) ∧
    (meanNonpositive ↔
      (P {omega : Omega |
        ¬ BddBelow (Set.range
          (fun t : NNReal => L.X t omega))}).toReal = 1) ∧
    (¬ meanNonpositive →
      (P {omega : Omega |
        BddBelow (Set.range
          (fun t : NNReal => L.X t omega))}).toReal = 1) := by
  exact ⟨
    Kyprianou.Ch04.limitingDrawdown_LaplaceTransform P F L hNotNegativeSubordinator,
    Kyprianou.Ch04.limitingDrawdown_nonpositiveMeanClassification P F L hNotNegativeSubordinator,
    Kyprianou.Ch04.limitingDrawdown_positiveMeanClassification P F L hNotNegativeSubordinator
  ⟩
