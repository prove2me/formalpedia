-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyStartTailRecurrenceV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:01:27.303414+00:00
-- url     : https://prove2.me/submissions/4b3ebf34-578e-44d7-9e16-99ce2b050bf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteArrivalIntensityV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartsNonemptyV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartTailMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyRegenerativeTailV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (∀ k : Nat, ∃ S : Set Omega, MeasurableSet S ∧
      S =ᵐ[P] {omega | ((k + 1 : Nat) : ENat) ≤ (busyStarts omega).encard}) ∧
    (P {omega | (1 : ENat) ≤ (busyStarts omega).encard}).toReal = 1 ∧
    ∀ k : Nat,
      (P {omega | ((k + 1 + 1 : Nat) : ENat) ≤ (busyStarts omega).encard}).toReal =
        (1 - p) * (P {omega | ((k + 1 : Nat) : ENat) ≤
          (busyStarts omega).encard}).toReal := by
  dsimp only
  letI : IsProbabilityMeasure P := L.isProbability
  have hrate := Kyprianou.Ch04.exercise46FiniteArrivalIntensityV1
    P G L lambda hlambda service hServicePositive hInputLaw
  have hfin : L.ν (Iio (0 : Real)) < ⊤ := by rw [hrate]; simp
  have hpos : 0 < (L.ν (Iio (0 : Real))).toReal := by
    rw [hrate, ENNReal.toReal_ofReal hlambda.le]
    exact hlambda
  have hne := Kyprianou.Ch04.exercise46BusyStartsNonemptyV1
    P G L hBV hDrift hfin hpos Wleft hWLeft
  refine ⟨Kyprianou.Ch04.exercise46BusyStartTailMeasurableV1 P G L Wleft hWLeft, ?_, ?_⟩
  · have he : {w : Omega | (1 : ENat) ≤
        {t : NNReal | 0 < t ∧ Wleft t w = 0 ∧
          0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}.encard}
        =ᵐ[P] (Set.univ : Set Omega) := by
      filter_upwards [hne] with w hw
      apply propext
      change (1 : ENat) ≤ _ ↔ True
      exact iff_true_intro (Set.one_le_encard_iff_nonempty.mpr hw)
    rw [measure_congr he]
    simp
  · exact Kyprianou.Ch04.exercise46BusyRegenerativeTailV1
      P G L hBV hDrift lambda hlambda service hServicePositive hInputLaw
      Wleft hWLeft rho hRho hSupercritical phi hphi hroot hmax
