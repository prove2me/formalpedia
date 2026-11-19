-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_positiveExpMoments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:16:02.560123+00:00
-- url     : https://prove2.me/submissions/c7becc71-79d4-4065-9918-bc01ed36821e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false




theorem solution
{Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))) :
    (∀ beta : ℝ, 0 ≤ beta →
        ∀ t : NNReal, Integrable
          (fun omega => Real.exp (beta * L.X t omega)) P) := by
  exact fun beta hbeta t => (L.laplace t beta hbeta).1

