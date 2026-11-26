-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PhysicalRecoveryClockProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:27:37.494828+00:00
-- url     : https://prove2.me/submissions/ff239b95-6693-492f-bc4f-fe870de8ef3f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46AbsoluteRecoveryStoppingV1
import Theorems.Thm_Kyprianou_Ch04_exercise46ShiftStrictPathKernelV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryKernelFiniteEventV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstServiceMarkLawV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstRestartProductLawV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstArrivalNotAntitoneV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FixedStrictRootTransformV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RestartKernelRecoveryProbabilityV1
import Theorems.Thm_Kyprianou_Ch04_exercise46ExtendedStoppedPathLawV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteRestartLawUnrestrictV1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (hPrefix : ∀ᵐ w ∂P,
      (∀ s : NNReal, s < (A w).untopD 0 → L.X s w = (s : Real)) ∧
      (∀ s : NNReal, L.X s w ≤ (s : Real)))
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x))
    (phi : Real) (hphi : 0 < phi) (hroot : L.ψ phi = 0)
    (hmax : ∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    IsStoppingTime G.rightCont R ∧
      (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service := by
  classical
  dsimp only
  letI : IsProbabilityMeasure P := L.isProbability
  let a : Omega → NNReal := fun w => (A w).untopD 0
  let R : Omega → WithTop NNReal := fun w =>
    ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧ (a w : Real) < L.X r w
      then (r : WithTop NNReal) else ⊤
  have hR : IsStoppingTime G.rightCont R :=
    Kyprianou.Ch04.exercise46AbsoluteRecoveryStoppingV1 P G L A hA
  refine ⟨hR,?_⟩
  let J : Omega → Real := fun w => -(L.X (a w) w -
    Function.leftLim (fun u : NNReal => L.X u w) (a w))
  let Z : Omega → (NNReal → Real) := fun w u => L.X (a w+u) w - L.X (a w) w
  let Y : Omega → (NNReal → Real) := fun w u => L.X u w
  have hFin : ∀ᵐ w ∂P, A w ≠ ⊤ :=
    hFirst.mono fun w hw => hw.1.trans_ne (WithTop.coe_ne_top)
  obtain ⟨hJ,hJL⟩ := Kyprianou.Ch04.exercise46FirstServiceMarkLawV1
    P G L A hA hFirst lambda hlambda service hServicePositive hInputLaw
  have hJP : ∀ᵐ w ∂P, 0 < J w :=
    hFirst.mono fun w hw => neg_pos.mpr (sub_neg.mpr hw.2.2.1)
  have hProd := Kyprianou.Ch04.exercise46FirstRestartProductLawV1 P G L A hA hFin
  obtain ⟨Lr,hX,_,_,_⟩ := avram_wave5_04_source_rightCont_levy_lift L
  have ha (w : Omega) (hw : A w ≠ ⊤) : A w = (a w : WithTop NNReal) :=
    (WithTop.coe_untop₀_of_ne_top (by simpa using hw)).symm
  have hL := Kyprianou.Ch04.exercise46ExtendedStoppedPathLawV1 P G.rightCont Lr A hA a ha
  rw [hX] at hL
  have hZ := (Kyprianou.Ch04.exercise46FiniteRestartLawUnrestrictV1 P A hFin Z Y
    hL.1 univ (hL.2 univ (fun s => by simpa using hA s))).1
  obtain ⟨K,hK,hKx,hKshift⟩ := Kyprianou.Ch04.exercise46ShiftStrictPathKernelV1 P G L
  have hEq := Kyprianou.Ch04.exercise46RecoveryKernelFiniteEventV1 P G L A hA hFirst hPrefix K hKshift
  have hnd := Kyprianou.Ch04.exercise46FirstArrivalNotAntitoneV1 P G L a
    (hFirst.mono fun w hw => hw.2.1) (hPrefix.mono fun w hw => hw.1)
  have ht := Kyprianou.Ch04.exercise46FixedStrictRootTransformV1 P G L hnd phi hphi hroot hmax
  exact Kyprianou.Ch04.exercise46RestartKernelRecoveryProbabilityV1
    P G L J Z hJ hZ service hJL hJP hProd K hK hKx R hR.measurable' hEq phi
    (fun x hx => ht x hx.le)
