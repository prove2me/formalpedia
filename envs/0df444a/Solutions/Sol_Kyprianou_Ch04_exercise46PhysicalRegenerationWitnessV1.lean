-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PhysicalRegenerationWitnessV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:24:06.140595+00:00
-- url     : https://prove2.me/submissions/ccad9537-f98d-4144-934f-b13b2e4fc7ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteArrivalIntensityV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpClockV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstArrivalLinearPrefixV1
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime
import Theorems.Thm_Kyprianou_Ch04_exercise46PhysicalRecoveryClockProbabilityV1
import Theorems.Thm_Kyprianou_Ch04_exercise46NoArrivalAtPrelevelV1
import Theorems.Thm_Kyprianou_Ch04_exercise46CommonBusyCountV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PhysicalBusySplitV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
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
    let S : Omega → Set NNReal := fun w => {t | 0 < t ∧ Wleft t w = 0 ∧
      0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    let Y : Omega → (NNReal → Real) := fun w u => L.X u w
    ∃ R : Omega → WithTop NNReal, IsStoppingTime G.rightCont R ∧
      ∃ C : (NNReal → Real) → ENNReal, Measurable C ∧
        (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service ∧
        (∀ᵐ w ∂P, C (Y w) = ((S w).encard : ENNReal)) ∧
        (∀ᵐ w ∂P,
          (R w ≠ ⊤ → C (Y w) = 1 +
            C (fun u => L.X ((R w).untopD 0 + u) w - L.X ((R w).untopD 0) w)) ∧
          (R w = ⊤ → C (Y w) = 1)) := by
  classical
  dsimp only
  have hRateEq := Kyprianou.Ch04.exercise46FiniteArrivalIntensityV1
    P G L lambda hlambda service hServicePositive hInputLaw
  have hFinite : L.ν (Iio (0 : Real)) < ⊤ := by rw [hRateEq]; exact ENNReal.ofReal_lt_top
  have hRate : 0 < (L.ν (Iio (0 : Real))).toReal := by
    rw [hRateEq,ENNReal.toReal_ofReal hlambda.le]
    exact hlambda
  let A : Omega → WithTop NNReal := fun w =>
    ⨅ u : NNReal, if 0 < u ∧ L.X u w -
      Function.leftLim (fun v : NNReal => L.X v w) u < 0
      then (u : WithTop NNReal) else ⊤
  have hA : IsStoppingTime G.rightCont A :=
    avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime L hBV hFinite
  have hFirst := Kyprianou.Ch04.exercise46FirstPhysicalJumpClockV1 P G L hBV hFinite hRate
  change (∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
    0 < (A w).untopD 0 ∧ L.X ((A w).untopD 0) w <
      Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
    ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
      L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u) at hFirst
  have hBefore : ∀ᵐ w ∂P, ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
      L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u :=
    hFirst.mono fun w hw => hw.2.2.2
  have hPrefix := Kyprianou.Ch04.exercise46FirstArrivalLinearPrefixV1 P G L
    hBV hDrift hFinite (fun w => (A w).untopD 0) hBefore
  let R : Omega → WithTop NNReal := fun w =>
    ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
      (((A w).untopD 0 : NNReal) : Real) < L.X r w
      then (r : WithTop NNReal) else ⊤
  have hRecovery := Kyprianou.Ch04.exercise46PhysicalRecoveryClockProbabilityV1
    P G L A hA hFirst hPrefix lambda hlambda service hServicePositive hInputLaw
    phi hphi hroot hmax
  change IsStoppingTime G.rightCont R ∧
    (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service at hRecovery
  have hNo := Kyprianou.Ch04.exercise46NoArrivalAtPrelevelV1 P G L hBV hDrift hFinite A hA
  obtain ⟨C,hC,hOriginal,hShift⟩ := Kyprianou.Ch04.exercise46CommonBusyCountV1 P G L Wleft hWLeft
  have hSplit := Kyprianou.Ch04.exercise46PhysicalBusySplitV1 P G L A hA hFirst hPrefix
    Wleft hWLeft hNo C hOriginal hShift
  exact ⟨R,hRecovery.1,C,hC,hRecovery.2,hOriginal,hSplit⟩
