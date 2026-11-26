-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkload_positiveTrafficLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:06:36.909958+00:00
-- url     : https://prove2.me/submissions/8b67afd3-90e1-4bc3-b30e-05c2dfccac79

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricMeasureExists
import Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricMeasureAtom
import Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricMeasureConvergence
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Theorem 4.10 (p. 100): weak workload limit, atom, geometric convolution and transient regime. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    let eta : Measure Real :=
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun x : Real =>
          L.ν (Set.Iio (-x)) /
            (ENNReal.ofReal L.drift * rho))
    let convPow : Nat → Measure Real :=
      Nat.rec (Measure.dirac (0 : Real))
        (fun _ mu => mu.conv eta)
    (0 < rho → rho < 1 →
      ∃ mu : Measure Real,
        IsProbabilityMeasure mu ∧
        IsProbabilityMeasure eta ∧
        mu {0} = 1 - rho ∧
        (∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B)) ∧
        (∀ w : Real, 0 ≤ w →
          let supX : NNReal → Omega → Real := fun t omega =>
            sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
          let W : NNReal → Omega → Real := fun t omega =>
            max w (supX t omega) - L.X t omega
          ∀ f : BoundedContinuousFunction Real Real,
            Tendsto
              (fun t : NNReal =>
                ∫ omega, f (W t omega) ∂P)
              atTop
              (nhds (∫ x : Real, f x ∂mu)))) := by
  intro rho eta convPow hr0 hr1
  obtain ⟨mu, hmu, heta, hSeries⟩ :=
    Kyprianou.Ch04.stationaryWorkloadGeometricMeasureExists
      P F L hBV hd hr0 hr1
  refine ⟨mu, hmu, heta, ?_, hSeries, ?_⟩
  · exact Kyprianou.Ch04.stationaryWorkloadGeometricMeasureAtom
      P F L hBV hd hr0 hr1 mu hSeries
  · exact Kyprianou.Ch04.stationaryWorkloadGeometricMeasureConvergence
      P F L hBV hd hr0 hr1 mu hmu hSeries
