-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyRegenerativeTailV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:38:45.717642+00:00
-- url     : https://prove2.me/submissions/7d02aac9-62e1-4eef-ab56-cb2732bce9ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46PhysicalRegenerationWitnessV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RegenerativePhysicalTailTransferV1
import Theorems.Thm_Kyprianou_Ch04_exercise46ExtendedStoppedPathLawV1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
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
    ∀ k : Nat,
      (P {omega | ((k + 1 + 1 : Nat) : ENat) ≤ (busyStarts omega).encard}).toReal =
        (1 - p) * (P {omega | ((k + 1 : Nat) : ENat) ≤
          (busyStarts omega).encard}).toReal := by
  classical
  dsimp only
  letI : IsProbabilityMeasure P := L.isProbability
  let S : Omega → Set NNReal := fun w => {t | 0 < t ∧ Wleft t w = 0 ∧
    0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
  let Y : Omega → (NNReal → Real) := fun w u => L.X u w
  obtain ⟨R, hR, C, hC, hq, hCard, hSplit⟩ :=
    Kyprianou.Ch04.exercise46PhysicalRegenerationWitnessV1 P G L hBV hDrift lambda hlambda
      service hServicePositive hInputLaw Wleft hWLeft rho hRho hSupercritical phi hphi hroot hmax
  let D : Set Omega := {w | R w ≠ ⊤}
  let a : Omega → NNReal := fun w => (R w).untopD 0
  let Z : Omega → (NNReal → Real) := fun w u => L.X (a w + u) w - L.X (a w) w
  have hD : MeasurableSet D := hR.measurableSet_eq_top.compl
  have hY : Measurable Y :=
    measurable_pi_lambda _ (fun t => (L.adapted t).mono (G.le t) le_rfl)
  obtain ⟨Lr, hX, _, _, _⟩ := avram_wave5_04_source_rightCont_levy_lift L
  have ha (w : Omega) (hw : R w ≠ ⊤) : R w = (a w : WithTop NNReal) :=
    (WithTop.coe_untop₀_of_ne_top (by simpa using hw)).symm
  have hL := Kyprianou.Ch04.exercise46ExtendedStoppedPathLawV1 P G.rightCont Lr R hR a ha
  rw [hX] at hL
  have hLaw : (P.restrict D).map Z = P D • P.map Y := by
    simpa only [univ_inter] using hL.2 univ (fun s => by simpa using hR s)
  have hs : ∀ᵐ w ∂P, (w ∈ D → C (Y w) = 1 + C (Z w)) ∧
      (w ∉ D → C (Y w) = 1) := by
    filter_upwards [hSplit] with w hw
    exact ⟨hw.1, fun h => hw.2 (not_not.mp h)⟩
  have hRec := Kyprianou.Ch04.exercise46RegenerativePhysicalTailTransferV1
    P S D hD Y Z hY hL.1 C hC _ hq hLaw hCard hs
  simpa only [sub_sub_cancel] using hRec
