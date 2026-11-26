-- Prove2me | solution 2 for Kyprianou.Ch04.exercise46BusyStartCountV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T16:04:20.895311+00:00
-- url     : https://prove2.me/submissions/a1e1e226-df1b-4dbc-a8ee-4d0c54473d6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartTailRecurrenceV2
import Theorems.Thm_Kyprianou_Ch04_exercise46GeometricCardFiniteV1
import Theorems.Thm_Kyprianou_Ch04_exercise46GeometricCardMassV2
import Theorems.Thm_Kyprianou_Ch04_exercise46ServiceLaplaceBoundsV1
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation)
    (hDrift : L.drift = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Set.Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν =
      ENNReal.ofReal lambda •
        (service.map (fun x : Real => -x)))
    (Wleft : NNReal -> Omega -> Real)
    (hWLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal =>
          sSup ((fun u : NNReal => L.X u omega) '' Set.Iic s) -
          L.X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Wleft t omega)))
    (rho : Real)
    (hRho : rho =
      lambda * (∫ y : Real, y ∂service))
    (hSupercritical : 1 < rho)
    (phi : Real) (hphi : 0 < phi) (hroot : L.ψ phi = 0)
    (hmax : ∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Iic t)
    let W : NNReal → Omega → Real := fun t omega => supX t omega - L.X t omega
    let busyStarts : Omega → Set NNReal := fun omega =>
      {t : NNReal | 0 < t ∧ Wleft t omega = 0 ∧ 0 < W t omega}
    let p : Real := 1 - ∫ y : Real, Real.exp (-phi * y) ∂service
    (∀ᵐ omega : Omega ∂P, (busyStarts omega).Finite) ∧
      ∀ k : Nat, (P {omega : Omega | (busyStarts omega).ncard = k + 1}).toReal =
        p * (1 - p) ^ k := by
  letI : IsProbabilityMeasure P := L.isProbability
  dsimp only
  let B : Omega → Set NNReal := fun omega =>
    {t | 0 < t ∧ Wleft t omega = 0 ∧
      0 < sSup ((fun s : NNReal => L.X s omega) '' Iic t) - L.X t omega}
  let p : Real := 1 - ∫ y : Real, Real.exp (-phi * y) ∂service
  have hb := Kyprianou.Ch04.exercise46ServiceLaplaceBoundsV1
    service hServicePositive phi hphi
  have hp : 0 < p := sub_pos.mpr hb.2
  have hp1 : p < 1 := by dsimp [p]; linarith [hb.1]
  obtain ⟨hmeas, hfirst, hrec⟩ := Kyprianou.Ch04.exercise46BusyStartTailRecurrenceV2
    P G L hBV hDrift lambda hlambda service hServicePositive hInputLaw
    Wleft hWLeft rho hRho hSupercritical phi hphi hroot hmax
  have htail (k : Nat) : (P {omega |
      ((k + 1 : Nat) : ENat) ≤ (B omega).encard}).toReal = (1 - p) ^ k := by
    induction k with
    | zero => simpa [B] using hfirst
    | succ k ih =>
      rw [pow_succ, mul_comm]
      rw [← ih]
      exact hrec k
  have hf := Kyprianou.Ch04.exercise46GeometricCardFiniteV1 P B p hp hp1 htail
  exact ⟨hf, Kyprianou.Ch04.exercise46GeometricCardMassV2
    P B p hp hp1 htail hmeas hf⟩
