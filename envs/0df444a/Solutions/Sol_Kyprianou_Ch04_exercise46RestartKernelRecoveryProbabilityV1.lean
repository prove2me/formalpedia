-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RestartKernelRecoveryProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:13:18.121837+00:00
-- url     : https://prove2.me/submissions/a1d87748-f94e-442a-9520-488a096c35f1

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46ProductKernelIntegralV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryIndicatorProbabilityV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (J : Omega → Real) (Z : Omega → (NNReal → Real))
    (hJ : Measurable J) (hZ : AEMeasurable Z P)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hJL : P.map J = service) (hJP : ∀ᵐ w ∂P, 0 < J w)
    (hLaw : P.map (fun w => (J w,Z w)) =
      (P.map J).prod (P.map (fun w t => L.X t w)))
    (K : Real × (NNReal → Real) → WithTop NNReal) (hK : Measurable K)
    (hKx : ∀ x : Real, 0 < x → ∀ w,
      K (x, fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w)
    (R : Omega → WithTop NNReal) (hR : Measurable R)
    (hEq : ∀ᵐ w ∂P, R w = ⊤ ↔ K (J w,Z w) = ⊤)
    (phi : Real)
    (hStrict : ∀ x : Real, 0 < x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-(0 : Real) *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
      = Real.exp (-phi * x)) :
    (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service := by
  classical
  let Y : Omega → (NNReal → Real) := fun w t => L.X t w
  have hY : Measurable Y :=
    measurable_pi_lambda _ (fun t => (L.adapted t).mono (G.le t) le_rfl)
  let f : Real × (NNReal → Real) → Real := fun z => if K z = ⊤ then 0 else 1
  have hf : Measurable f :=
    Measurable.ite (hK (measurableSet_singleton ⊤)) measurable_const measurable_const
  have hb (z : Real × (NNReal → Real)) : ‖f z‖ ≤ 1 := by
    dsimp [f]
    split <;> norm_num
  have ht : (∫ w, if R w = ⊤ then (0 : Real) else
      Real.exp (-(0 : Real) * (((R w).untopD 0 : NNReal) : Real)) ∂P) =
      ∫ y : Real, Real.exp (-phi * y) ∂service := by
    calc
      _ = ∫ w, f (J w,Z w) ∂P := by
        apply integral_congr_ae
        filter_upwards [hEq] with w hw
        simp only [f, neg_zero, zero_mul, Real.exp_zero, hw]
      _ = ∫ y, (∫ w, f (y,Y w) ∂P) ∂(P.map J) :=
        Kyprianou.Ch04.exercise46ProductKernelIntegralV1 P J Z Y
          hJ.aemeasurable hZ hY hLaw f hf hb
      _ = ∫ y, Real.exp (-phi * y) ∂(P.map J) := by
        apply integral_congr_ae
        filter_upwards [(ae_map_iff hJ.aemeasurable measurableSet_Ioi).mpr hJP] with y hy
        simpa only [f, Y, hKx y hy, neg_zero, zero_mul, Real.exp_zero] using hStrict y hy
      _ = _ := by rw [hJL]
  exact Kyprianou.Ch04.exercise46RecoveryIndicatorProbabilityV1 P R hR _ ht
