-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkloadGeometricMeasureConvergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:01.106359+00:00
-- url     : https://prove2.me/submissions/ac2ef8ce-7c29-4e52-85ab-5794b94ffd33

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_subcriticalZeroInitialWorkloadLimitLaw
import Theorems.Thm_Kyprianou_Ch04_subcriticalGeometricWorkloadLawTransform
import Theorems.Thm_Kyprianou_Ch04_subcriticalInitialWorkloadLimitTransfer
import Theorems.Thm_Kyprianou_Ch04_nonnegativeProbabilityLaplaceUnique
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Identify the limiting law by Laplace uniqueness and transfer the initial workload. -/
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
        IsProbabilityMeasure mu →
        (∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B)) →
        ∀ w : Real, 0 ≤ w →
          let supX : NNReal → Omega → Real := fun t omega =>
            sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
          let W : NNReal → Omega → Real := fun t omega =>
            max w (supX t omega) - L.X t omega
          ∀ f : BoundedContinuousFunction Real Real,
            Tendsto
              (fun t : NNReal =>
                ∫ omega, f (W t omega) ∂P)
              atTop
              (nhds (∫ x : Real, f x ∂mu)) := by
  intro rho eta convPow hr0 hr1 mu hmu hLaw w hw supX W f
  obtain ⟨nu,hnu,hnu0,hnuLap,hnuLim⟩ :=
    Kyprianou.Ch04.subcriticalZeroInitialWorkloadLimitLaw P F L hBV hd hr0 hr1
  obtain ⟨hmu0,hmuLap⟩ :=
    Kyprianou.Ch04.subcriticalGeometricWorkloadLawTransform P F L hBV hd hr0 hr1 mu hmu hLaw
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure nu := hnu
  have he : nu = mu :=
    Kyprianou.Ch04.nonnegativeProbabilityLaplaceUnique nu mu hnu0 hmu0
      (fun a ha => (hnuLap a ha).trans (hmuLap a ha).symm)
  subst nu
  exact Kyprianou.Ch04.subcriticalInitialWorkloadLimitTransfer P F L hBV hd hr0 hr1
    w hw f _ (hnuLim f)
