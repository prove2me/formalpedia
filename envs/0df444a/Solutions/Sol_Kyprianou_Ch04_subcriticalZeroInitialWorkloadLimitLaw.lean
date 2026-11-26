-- Prove2me | solution 1 for Kyprianou.Ch04.subcriticalZeroInitialWorkloadLimitLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:00.248018+00:00
-- url     : https://prove2.me/submissions/53f29d66-551b-46e3-b610-8c1e76c41387

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_subcriticalZeroInitialWorkloadWeakLimit
import Theorems.Thm_Kyprianou_Ch04_subcriticalWeakLimitLaplaceTransform
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The zero-initial workload converges weakly to a nonnegative law with the subcritical Laplace ratio. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∃ mu : Measure ℝ, IsProbabilityMeasure mu ∧ mu (Iio 0) = 0 ∧
      (∀ a : ℝ, 0 < a → (∫ x, Real.exp (-a*x) ∂mu) = (L.drift-M.toReal)*a/L.ψ a) ∧
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
          atTop (nhds (∫ x, f x ∂mu))) := by
  intro M rho hr0 hr1
  obtain ⟨nu,hnu,hnu0,hweak⟩ :=
    Kyprianou.Ch04.subcriticalZeroInitialWorkloadWeakLimit P F L hBV hd hr0 hr1
  exact ⟨nu,hnu,hnu0,
    Kyprianou.Ch04.subcriticalWeakLimitLaplaceTransform P F L hBV hd hr0 hr1 nu hnu0 hweak,
    hweak⟩
