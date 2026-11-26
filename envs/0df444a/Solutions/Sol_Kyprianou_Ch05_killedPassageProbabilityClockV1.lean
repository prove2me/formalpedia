-- Prove2me | solution 1 for Kyprianou.Ch05.killedPassageProbabilityClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:59:56.762986+00:00
-- url     : https://prove2.me/submissions/f17a6a12-37a0-4822-81b7-c152703fc56c

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_strictKilledClockFromUnkilledV1
import Theorems.Thm_Kyprianou_Ch05_killedPathRandomClockSurvivalV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (x : ℝ) (T : (NNReal → ℝ) → ENNReal) (hTm : Measurable T)
    (hT : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
      T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t})) :
    P {w | PassageFinite Y death x w} =
      ∫⁻ w, if T (fun t => Y t w) ≠ ⊤ then
        ENNReal.ofReal (Real.exp (-eta*(T (fun t => Y t w)).toReal)) else 0 ∂P := by
  classical
  let W : Omega → (NNReal → ℝ) := fun w t => Y t w
  have hW : AEMeasurable W P :=
    Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1 P Y hKilled.1.1.cadlag_ae
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1)
  have he : {w | PassageFinite Y death x w} =ᵐ[P]
      {w | W w ∈ (univ : Set (NNReal → ℝ)) ∧ T (W w) < death w} := by
    filter_upwards [hKilled.1.2] with w hw
    apply propext
    have hk := strictKilledClockFromUnkilledV1 Y death x w (T (W w))
      (hT _ hw (congrFun hKilled.1.1.start_zero w))
    change (strictUpcrossing Y death x w : ENNReal) ≠ ⊤ ↔
      (W w ∈ (univ : Set (NNReal → ℝ)) ∧ T (W w) < (death w : ENNReal))
    rw [hk]
    by_cases h : T (W w) < (death w : ENNReal)
    · simp [h]
      change T (W w) ≠ (⊤ : ENNReal)
      exact ne_of_lt (lt_of_lt_of_le h (le_top : (death w : ENNReal) ≤ ⊤))
    · simp [h]
      rfl
  rw [measure_congr he,killedPathRandomClockSurvivalV1 P Y death eta hKilled T hTm
    univ MeasurableSet.univ]
  simp only [mem_univ,true_and]
  have hf : Measurable (fun f : NNReal → ℝ => if T f ≠ ⊤ then
      ENNReal.ofReal (Real.exp (-eta*(T f).toReal)) else 0) := by
    exact Measurable.ite ((measurableSet_singleton ⊤).preimage hTm).compl
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((ENNReal.measurable_toReal.comp hTm).const_mul (-eta)))) measurable_const
  exact lintegral_map' hf.aemeasurable hW
