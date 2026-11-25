-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkloadGeometricMeasureAtom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:03:54.531776+00:00
-- url     : https://prove2.me/submissions/146602c0-1001-4a34-9f95-0e02c61e184d

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_trafficIntegratedNegativeTailProbability
import Theorems.Thm_Kyprianou_Ch04_convolutionPowerPreservesProbability
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_positive_convolution_powers_no_atom
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
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
      ∀ mu : Measure Real,
        (∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B)) →
        mu {0} = 1 - rho := by
  intro rho eta convPow hr0 hr1 mu hSeries
  have heta : IsProbabilityMeasure eta :=
    Kyprianou.Ch04.trafficIntegratedNegativeTailProbability
      P F L hBV hd hr0 hr1
  letI : IsProbabilityMeasure eta := heta
  have hpow : ∀ n : Nat, IsProbabilityMeasure (convPow n) := by
    simpa only [convPow] using
      (Kyprianou.Ch04.convolutionPowerPreservesProbability eta)
  have hsf : ∀ n : Nat, SFinite (convPow n) := by
    intro n
    letI : IsProbabilityMeasure (convPow n) := hpow n
    infer_instance
  have hac : eta ≪ (volume : Measure Real) := by
    dsimp only [eta]
    exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hsucc : ∀ n : Nat, convPow (n + 1) = eta.conv (convPow n) := by
    intro n
    letI : SFinite (convPow n) := hsf n
    change (convPow n).conv eta = eta.conv (convPow n)
    exact Measure.conv_comm _ _
  have hzero :=
    AvramDividend.Classical.geometric_renewal_positive_convolution_powers_no_atom
      eta convPow hsf hac hsucc
  rw [hSeries {0} (measurableSet_singleton 0)]
  rw [tsum_eq_single 0]
  · change (1 - rho) * rho ^ 0 * Measure.dirac (0 : Real) {0} = 1 - rho
    simp
  · intro n hn
    rw [hzero n (Nat.pos_of_ne_zero hn), mul_zero]
