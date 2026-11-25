-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RandomWeakPassageTransformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:52:49.059033+00:00
-- url     : https://prove2.me/submissions/0bddda67-5ebe-40c6-86c7-d9797f8693c7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46NonzeroStrictPassageNotAntitoneV1
import Theorems.Thm_Kyprianou_Ch04_exercise46WeakClockEqualsStrictOfRateOneV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RandomStrictPassageTransformV1
import Theorems.Thm_Kyprianou_Ch03_upwardFirstPassageLaplaceTransform
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (service : Measure Real) [IsProbabilityMeasure service]
    (J : Omega → Real) (hJLaw : P.map J = service)
    (hJPositive : ∀ᵐ omega ∂P, 0 < J omega)
    (hIndependent : Indep
      (MeasurableSpace.comap J inferInstance)
      (MeasurableSpace.comap (fun omega : Omega => fun t : NNReal => L.X t omega)
        inferInstance) P)
    (beta phi : Real) (hb : 0 ≤ beta) (hp : 0 ≤ phi)
    (hStrict : ∀ x : Real, 0 ≤ x →
      (∫ omega, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) omega = ⊤
        then (0 : Real) else Real.exp (-beta *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) omega).untopD 0 : NNReal) : Real)) ∂P)
        = Real.exp (-phi * x)) :
    let B : Omega → WithTop NNReal := fun omega =>
      sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ J omega ≤ L.X t omega}
    AEMeasurable B P ∧
      (∫ omega, if B omega = ⊤ then (0 : Real)
        else Real.exp (-beta * (((B omega).untopD 0 : NNReal) : Real)) ∂P) =
      ∫ y : Real, Real.exp (-phi * y) ∂service := by
  dsimp only
  have hJ : AEMeasurable J P := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hJLaw
    have hz : service univ = 0 := by rw [← hJLaw]; simp
    simpa using hz
  have hInd : IndepFun J (fun w : Omega => fun t : NNReal => L.X t w) P := hIndependent
  have hnd := Kyprianou.Ch04.exercise46NonzeroStrictPassageNotAntitoneV1
    P G L beta (by rw [hStrict 1 zero_le_one]; exact Real.exp_ne_zero _)
  obtain ⟨phi1, hp1, _, _, hs1⟩ := Kyprianou.Ch03.upwardFirstPassageLaplaceTransform
    P G L hnd 1 zero_le_one
  have hEq := Kyprianou.Ch04.exercise46WeakClockEqualsStrictOfRateOneV1
    P G L J hJ hJPositive hInd phi1 hp1
    (fun x hx => hs1 x hx.le
      (fun w => (Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0)
      (fun w h => (WithTop.coe_untop₀_of_ne_top (by simpa using h)).symm))
  obtain ⟨hSm, hS⟩ := Kyprianou.Ch04.exercise46RandomStrictPassageTransformV1
    P G L J hJ hJPositive hInd beta phi hb (fun x hx => hStrict x hx.le)
  refine ⟨hSm.congr hEq.symm, ?_⟩
  calc
    _ = _ := integral_congr_ae
      (hEq.fun_comp (fun z : WithTop NNReal =>
        if z = ⊤ then 0 else Real.exp (-beta * (((z.untopD 0 : NNReal) : Real)))))
    _ = ∫ w, Real.exp (-phi * J w) ∂P := hS
    _ = _ := by rw [← hJLaw]; exact (integral_map hJ (f := fun y : Real => Real.exp (-phi * y))
      (by fun_prop)).symm
