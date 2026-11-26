-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotentialSurvivalFactorGeneralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:17:38.61381+00:00
-- url     : https://prove2.me/submissions/071710ef-f306-4230-b3a5-4df86bf6221f

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (f : ℝ → ENNReal) (hf : Measurable f) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ w in {w : Omega | (Real.toNNReal t : WithTop NNReal) < death w},
        f (Y (Real.toNNReal t) w) ∂P) =
    ENNReal.ofReal (Real.exp (-eta*t)) * ∫⁻ v, f v ∂(P.map (Y (Real.toNNReal t))) := by
  classical
  let E : Set Omega := {w | (Real.toNNReal t : WithTop NNReal) < death w}
  have hE : MeasurableSet E := hKilled.2.2.1 measurableSet_Ioi
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1 (Real.toNNReal t)
  have h0 : IndepFun death (fun w : Omega => fun s : NNReal => Y s w) P :=
    hKilled.2.2.2.2.2
  have hJ : Measurable ((Ioi (Real.toNNReal t : WithTop NNReal)).indicator
      (1 : WithTop NNReal → ENNReal)) := measurable_const.indicator measurableSet_Ioi
  have hi := h0.comp hJ (hf.comp (measurable_pi_apply (Real.toNNReal t)))
  change IndepFun (E.indicator (1 : Omega → ENNReal))
    (fun w => f (Y (Real.toNNReal t) w)) P at hi
  have hfact := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    ((measurable_const.indicator hE).aemeasurable) (hf.comp_aemeasurable hm) hi
  have hsurv := hKilled.2.2.2.2.1 (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht] at hsurv
  change P E = _ at hsurv
  change (∫⁻ w in E, f (Y (Real.toNNReal t) w) ∂P) = _
  rw [← lintegral_indicator hE]
  have he : E.indicator (fun w => f (Y (Real.toNNReal t) w)) =
      fun w => E.indicator 1 w * f (Y (Real.toNNReal t) w) := by
    simpa only [Pi.one_apply,one_mul] using funext
      (fun w => indicator_mul_left E (1 : Omega → ENNReal)
        (fun w => f (Y (Real.toNNReal t) w)) (i := w))
  rw [he]
  calc
    _ = (∫⁻ w, E.indicator (1 : Omega → ENNReal) w ∂P) *
        ∫⁻ w, f (Y (Real.toNNReal t) w) ∂P := hfact
    _ = _ := by rw [lintegral_indicator_one hE,hsurv,lintegral_map' hf.aemeasurable hm]
