-- Prove2me | solution 1 for Kyprianou.Ch04.smallCompensatedRealExpBandLimitGeneral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:16:38.510087+00:00
-- url     : https://prove2.me/submissions/222bf435-4f09-4dfb-93bb-e4ecdae1cc91

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpKernelIntegrableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Dominated convergence of the real compensated small-jump exponent. -/
theorem solution
    (T : LevyKhintchineTriple)
    (e : Nat → Real) (he : ∀ n, 0 < e n ∧ e n < 1)
    (hzero : Tendsto e atTop (nhds 0))
    (beta : Real) :
    Tendsto (fun n => ∫ x in {x : Real | e n ≤ |x| ∧ |x| < 1},
      (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure) atTop
      (nhds (∫ x in Ioo (-1 : Real) 1,
        (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure)) := by
  let g (x : ℝ) := Real.exp (beta*x)-1-beta*x
  let S := Ioo (-1 : ℝ) 1
  let mu := T.levyMeasure.restrict S
  let B (n : ℕ) := {x : ℝ | e n ≤ |x| ∧ |x| < 1}
  have hi : Integrable g mu := Kyprianou.Ch03.momentSmallJumpKernelIntegrableV1 T beta
  have hb (n : ℕ) : MeasurableSet (B n) :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hp : ∀ᵐ x ∂mu, Tendsto (fun n => (B n).indicator g x) atTop (nhds (g x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    by_cases hz : x = 0
    · subst x
      simpa [g, B, Set.indicator_apply, (he _).1.not_ge] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · apply (tendsto_congr' (show (fun n => (B n).indicator g x) =ᶠ[atTop]
        (fun _ => g x) from ?_)).mpr tendsto_const_nhds
      filter_upwards [hzero.eventually (eventually_lt_nhds (abs_pos.mpr hz))] with n hn
      exact Set.indicator_of_mem (show x ∈ B n from ⟨hn.le, abs_lt.mpr hx⟩) g
  have hD := tendsto_integral_of_dominated_convergence (μ := mu)
    (F := fun n => (B n).indicator g) (f := g)
    (fun x => ‖g x‖) (fun n => (hi.indicator (hb n)).aestronglyMeasurable) hi.norm
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ B n <;> simp [Set.indicator_apply, hx]) hp
  simp_rw [integral_indicator (hb _), mu,
    Measure.restrict_restrict_of_subset (show B _ ⊆ S from fun x hx => abs_lt.mp hx.2)] at hD
  exact hD
