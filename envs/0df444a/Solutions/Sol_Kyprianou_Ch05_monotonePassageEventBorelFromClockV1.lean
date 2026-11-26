-- Prove2me | solution 1 for Kyprianou.Ch05.monotonePassageEventBorelFromClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:26:42.082222+00:00
-- url     : https://prove2.me/submissions/f6480fac-01f7-4632-99de-5997bfafb14c

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_passageBoundaryBorelVersionsV1
import Theorems.Thm_Kyprianou_Ch05_strictKilledClockFromUnkilledV1
import Theorems.Thm_Kyprianou_Ch05_killedMarkedEventAtClockV1
import Theorems.Thm_Kyprianou_Ch05_monotoneMarkedCrossingSumV1
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
    (Y Yleft : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x)
    (T : (NNReal → ℝ) → ENNReal) (hTm : Measurable T)
    (hT : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t})) :
    ∃ C : Set (NNReal → ℝ), MeasurableSet C ∧
      ({w | PassageFinite Y death x w ∧ 0 < passageOvershoot Y death x w ∧
          passageOvershoot Y death x w ∈ A ∧ passageUndershoot Y Yleft death x w ∈ B}
        =ᵐ[P] {w | (fun t => Y t w) ∈ C ∧ T (fun t => Y t w) < death w}) ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        (if f ∈ C ∧ T f ≠ ⊤ then ENNReal.ofReal (Real.exp (-eta*(T f).toReal)) else 0) =
          ∑' t : NNReal, if 0 < t ∧ f t > x ∧
            Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
            f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
            ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  classical
  let t : (NNReal → ℝ) → NNReal := fun f => (T f).toNNReal
  obtain ⟨R,L,hR,hL,hReq,hLeq⟩ := passageBoundaryBorelVersionsV1 t
    (ENNReal.measurable_toNNReal.comp hTm)
  let C : Set (NNReal → ℝ) := {f | 0 < t f ∧ x < R f ∧
    L f ∈ Icc (0 : ℝ) x ∧ R f - x ∈ A ∧ x - L f ∈ B}
  have ht : Measurable t := ENNReal.measurable_toNNReal.comp hTm
  have hC : MeasurableSet C := (measurableSet_lt measurable_const ht).inter
    ((measurableSet_lt measurable_const hR).inter
    ((measurableSet_Icc.preimage hL).inter
    ((hA.preimage (hR.sub_const x)).inter (hB.preimage (hL.const_sub x)))))
  refine ⟨C,hC,?_,?_⟩
  · filter_upwards [hKilled.1.2,hKilled.1.1.cadlag_ae,hLeft] with w hm hc hl
    let f : NNReal → ℝ := fun s => Y s w
    have hz : f 0 = 0 := congrFun hKilled.1.1.start_zero w
    have hclock := strictKilledClockFromUnkilledV1 Y death x w (T f) (hT f hm hz)
    have hleft (s : NNReal) (hs : 0 < s) : Yleft s w = Function.leftLim f s := by
      letI : (nhdsWithin s (Iio s)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,hs⟩
      exact (leftLim_eq_of_tendsto (hl s hs)).symm
    have he := killedMarkedEventAtClockV1 Y Yleft death x hx w A B hBp hz
      (T f) hclock hleft
    apply propext
    change (PassageFinite Y death x w ∧ 0 < passageOvershoot Y death x w ∧
      passageOvershoot Y death x w ∈ A ∧ passageUndershoot Y Yleft death x w ∈ B) ↔
      f ∈ C ∧ T f < (death w : ENNReal)
    refine he.trans ?_
    change ((0 < t f ∧ x < f (t f) ∧ Function.leftLim f (t f) ∈ Icc (0 : ℝ) x ∧
      f (t f) - x ∈ A ∧ x - Function.leftLim f (t f) ∈ B) ∧
      T f < (death w : ENNReal)) ↔ f ∈ C ∧ T f < (death w : ENNReal)
    by_cases hp : 0 < t f
    · simp only [C,mem_setOf_eq,hReq f (hc (t f)).1,hLeq f hp hm,t]
    · simp [C,hp,t] at *
  · intro f hm hz hr hl
    have he := monotoneMarkedCrossingSumV1 f hm x eta A B (T f) (hT f hm hz)
    by_cases hp : 0 < t f
    · simpa only [C,mem_setOf_eq,hReq f (hr (t f)),hLeq f hp hm,t,and_assoc] using he
    · have hn : ¬ 0 < (T f).toNNReal := hp
      simpa [C,hp,hn,t] using he
