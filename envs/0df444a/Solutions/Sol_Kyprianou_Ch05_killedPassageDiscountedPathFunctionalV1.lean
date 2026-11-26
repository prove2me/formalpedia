-- Prove2me | solution 1 for Kyprianou.Ch05.killedPassageDiscountedPathFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:20:53.371328+00:00
-- url     : https://prove2.me/submissions/5a2a5066-e367-40cf-a8cc-234fa7c3187c

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_monotonePassageClockBorelV1
import Theorems.Thm_Kyprianou_Ch05_monotonePassageEventBorelFromClockV1
import Theorems.Thm_Kyprianou_Ch05_killedPathRandomClockSurvivalV1
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
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x) :
    ∃ H : (NNReal → ℝ) → ENNReal, Measurable H ∧
      positiveJointPassageLaw P Y Yleft death x A B =
        ∫⁻ f, H f ∂(P.map (fun w t => Y t w)) ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        H f = ∑' t : NNReal, if 0 < t ∧ f t > x ∧
          Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
          ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  classical
  obtain ⟨T,hTm,hT⟩ := monotonePassageClockBorelV1 x hx
  obtain ⟨C,hC,hEvent,hSum⟩ := monotonePassageEventBorelFromClockV1
    P Y Yleft death eta hKilled hLeft x hx A B hA hB hAp hBp T hTm hT
  let H : (NNReal → ℝ) → ENNReal := fun f =>
    if f ∈ C ∧ T f ≠ ⊤ then ENNReal.ofReal (Real.exp (-eta*(T f).toReal)) else 0
  have hTop : MeasurableSet {f | T f ≠ ⊤} :=
    (measurableSet_singleton (⊤ : ENNReal)).compl.preimage hTm
  have hH : Measurable H := Measurable.ite (hC.inter hTop)
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((ENNReal.measurable_toReal.comp hTm).const_mul (-eta)))) measurable_const
  refine ⟨H,hH,?_,hSum⟩
  unfold positiveJointPassageLaw
  rw [measure_congr hEvent]
  exact killedPathRandomClockSurvivalV1 P Y death eta hKilled T hTm C hC
