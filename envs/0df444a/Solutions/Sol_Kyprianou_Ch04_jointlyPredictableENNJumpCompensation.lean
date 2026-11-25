-- Prove2me | solution 1 for Kyprianou.Ch04.jointlyPredictableENNJumpCompensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:47:47.109595+00:00
-- url     : https://prove2.me/submissions/335dfe4c-0576-4c7e-a6b1-3c153ad9d111

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_predictableRectangleCountFactorisation
import Theorems.Thm_Kyprianou_Ch04_predictableCompensationFromRectangleCounts
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (psi : Real → Real → Omega → ENNReal)
    (hPsi : Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2)) :
    ∀ t : NNReal,
      (∫⁻ omega, (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
        psi z.1 z.2 omega ∂(N.N omega)) ∂P) =
      (∫⁻ omega, (∫⁻ s in Set.Icc (0 : Real) (t : Real),
        (∫⁻ x, psi s x omega ∂levyMeasure) ∂volume) ∂P) := by
  have hRect := predictableRectangleCountFactorisation P levyMeasure F N hFuture
  exact predictableCompensationFromRectangleCounts P levyMeasure F N hRect psi hPsi
