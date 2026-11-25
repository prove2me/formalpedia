-- Prove2me | solution 1 for Kyprianou.Ch04.predictableSquaredKernelCompensationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T16:04:17.166728+00:00
-- url     : https://prove2.me/submissions/8b310ec4-8b02-46f3-95ce-3518bcaea1fc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
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
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (t : NNReal) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      ENNReal.ofReal ((phi z.1 z.2 w)^2) ∂(N.N w) ∂P) =
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal ((phi s x w)^2) ∂levyMeasure ∂volume ∂P) := by
  let psi (s x : ℝ) (w : Omega) := (phi s x w)^2
  have hp : IsAdmissiblePoissonKernel P F psi := by
    refine ⟨fun s x w => sq_nonneg _, hPhi.2.1.pow_const (2 : Nat), ?_, ?_⟩
    · intro r
      exact (hPhi.2.2.1 r).pow_const (2 : Nat)
    · intro x
      filter_upwards [hCommon] with w hw
      intro r hr
      exact (hw x r hr).pow 2
  have hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (r : NNReal), 0 < r →
      Tendsto (fun s : ℝ => psi s x w) (nhdsWithin (r : ℝ) (Set.Iio (r : ℝ)))
        (nhds (psi (r : ℝ) x w)) := by
    filter_upwards [hCommon] with w hw
    intro x r hr
    exact (hw x r hr).pow 2
  exact Kyprianou.Ch04.nonnegativePredictableJumpCompensationCommonNullV2
    P levyMeasure F N hFuture psi hp hc t
