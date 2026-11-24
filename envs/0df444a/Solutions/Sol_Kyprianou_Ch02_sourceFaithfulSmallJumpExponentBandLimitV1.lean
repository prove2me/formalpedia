-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulSmallJumpExponentBandLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:18:11.67315+00:00
-- url     : https://prove2.me/submissions/17c7fe56-9748-4fe2-8249-c94fda90caa8

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch02

theorem solution
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hzero : Tendsto ε atTop (nhds 0))
    (t : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | ε n ≤ |x| ∧ |x| < 1},
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
      atTop (nhds (Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in Set.Ioo (-1 : ℝ) 1,
          ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) := by
  classical
  let f := ProbabilityTheory.levyCompensatedIntegrand ξ
  let S (n : ℕ) : Set ℝ := {x | ε n ≤ |x| ∧ |x| < 1}
  let U : Set ℝ := Set.Ioo (-1) 1
  have hI : Integrable f levyMeasure :=
    ProbabilityTheory.integrable_levyCompensatedIntegrand hlevyMeasure ξ
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hU : MeasurableSet U := measurableSet_Ioo
  have hlim : Tendsto
      (fun n => ∫ x, (S n).indicator f x ∂levyMeasure)
      atTop (nhds (∫ x, U.indicator f x ∂levyMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro n
      exact (hI.indicator (hS n)).aestronglyMeasurable
    · exact hI.norm
    · intro n
      exact ae_of_all _ (fun x => by
        by_cases hx : x ∈ S n
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx])
    · apply ae_of_all
      intro x
      by_cases hx : |x| < 1
      · have hu : x ∈ U := abs_lt.mp hx
        by_cases hx0 : x = 0
        · subst x
          have hf : f 0 = 0 := by
            simp [f, ProbabilityTheory.levyCompensatedIntegrand]
          have he (n : ℕ) : (S n).indicator f 0 = 0 := by
            simp [Set.indicator_apply, hf]
          simp [he, Set.indicator_of_mem hu, hf]
        · have hp : 0 < |x| := abs_pos.mpr hx0
          have he : ∀ᶠ n in atTop, ε n < |x| :=
            (tendsto_order.1 hzero).2 _ hp
          rw [Set.indicator_of_mem hu]
          apply tendsto_const_nhds.congr'
          filter_upwards [he] with n hn
          exact (Set.indicator_of_mem
            (show x ∈ S n from ⟨hn.le, hx⟩) f).symm
      · have hu : x ∉ U := fun h => hx (abs_lt.mpr h)
        have he (n : ℕ) : x ∉ S n := fun h => hx h.2
        simp [Set.indicator_of_notMem hu, Set.indicator_of_notMem (he _)]
  have hEq : (fun n => ∫ x, (S n).indicator f x ∂levyMeasure) =
      (fun n => ∫ x in S n, f x ∂levyMeasure) := by
    funext n
    exact integral_indicator (hS n)
  rw [hEq, integral_indicator hU] at hlim
  have hm : Tendsto
      (fun n => (((t : ℝ) : ℂ)) * ∫ x in S n, f x ∂levyMeasure)
      atTop (nhds ((((t : ℝ) : ℂ)) * ∫ x in U, f x ∂levyMeasure)) :=
    tendsto_const_nhds.mul hlim
  exact Complex.continuous_exp.continuousAt.tendsto.comp hm
