-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkloadGeometricMeasureExists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:00:42.632931+00:00
-- url     : https://prove2.me/submissions/8d574f88-c909-4320-93f0-84f613aca5ce

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_trafficIntegratedNegativeTailProbability
import Theorems.Thm_Kyprianou_Ch04_geometricMixtureOfProbabilityMeasures
import Theorems.Thm_Kyprianou_Ch04_convolutionPowerPreservesProbability
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The exact stationary geometric-convolution measure exists and has unit mass. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
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
    0 < rho → rho < 1 →
      ∃ mu : Measure Real,
        IsProbabilityMeasure mu ∧
        IsProbabilityMeasure eta ∧
        ∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B) := by
  intro rho eta convPow hr0 hr1
  have heta : IsProbabilityMeasure eta :=
    Kyprianou.Ch04.trafficIntegratedNegativeTailProbability
      P F L hBV hd hr0 hr1
  letI : IsProbabilityMeasure eta := heta
  have hpow : ∀ n : Nat, IsProbabilityMeasure (convPow n) := by
    simpa only [convPow] using
      (Kyprianou.Ch04.convolutionPowerPreservesProbability eta)
  let mu : Measure Real :=
    Measure.sum (fun n : Nat => ((1 - rho) * rho ^ n) • convPow n)
  have hmu : IsProbabilityMeasure mu :=
    Kyprianou.Ch04.geometricMixtureOfProbabilityMeasures rho hr1 convPow hpow
  refine ⟨mu, hmu, heta, ?_⟩
  intro B hB
  change (Measure.sum
    (fun n : Nat => ((1 - rho) * rho ^ n) • convPow n)) B =
      ∑' n : Nat, ((1 - rho) * rho ^ n) * (convPow n B)
  rw [Measure.sum_apply _ hB]
  simp_rw [Measure.smul_apply, smul_eq_mul]
