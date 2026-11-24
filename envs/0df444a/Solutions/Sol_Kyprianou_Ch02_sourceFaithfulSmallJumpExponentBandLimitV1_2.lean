-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulSmallJumpExponentBandLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:19:23.830914+00:00
-- url     : https://prove2.me/submissions/85d8d52f-d939-4b1f-baa3-d661e0d659f6

import Mathlib
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

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
  let g := ProbabilityTheory.levyCompensatedIntegrand ξ
  let B := fun n : ℕ => {x : ℝ | ε n ≤ |x| ∧ |x| < 1}
  have hb : ∀ n, MeasurableSet (B n) := fun n =>
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hi : Integrable g levyMeasure := integrable_levyCompensatedIntegrand hlevyMeasure ξ
  have heq : ∀ x : ℝ, ∀ᶠ n in atTop,
      (B n).indicator g x = (Set.Ioo (-1 : ℝ) 1).indicator g x := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [g, levyCompensatedIntegrand, Set.indicator_apply]
    by_cases hsmall : |x| < 1
    · filter_upwards [hzero.eventually (eventually_lt_nhds (abs_pos.mpr hx))] with n hn
      rw [Set.indicator_of_mem (show x ∈ B n from ⟨hn.le, hsmall⟩),
        Set.indicator_of_mem (show x ∈ Set.Ioo (-1 : ℝ) 1 from abs_lt.mp hsmall)]
    · exact Eventually.of_forall fun n => by
        rw [Set.indicator_of_notMem (show x ∉ B n from fun h => hsmall h.2),
          Set.indicator_of_notMem (show x ∉ Set.Ioo (-1 : ℝ) 1 from fun h => hsmall (abs_lt.mpr h))]
  have hD := tendsto_integral_of_dominated_convergence (μ := levyMeasure)
    (F := fun n => (B n).indicator g) (f := (Set.Ioo (-1 : ℝ) 1).indicator g)
    (fun x => ‖g x‖) (fun n => (hi.indicator (hb n)).aestronglyMeasurable) hi.norm
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ B n <;> simp [Set.indicator_apply, hx])
    (Eventually.of_forall fun x => (tendsto_congr' (show (fun n => (B n).indicator g x) =ᶠ[atTop] (fun _ => (Set.Ioo (-1 : ℝ) 1).indicator g x) from heq x)).mpr tendsto_const_nhds)
  simp_rw [integral_indicator (hb _), integral_indicator measurableSet_Ioo] at hD
  exact (Complex.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul hD)
