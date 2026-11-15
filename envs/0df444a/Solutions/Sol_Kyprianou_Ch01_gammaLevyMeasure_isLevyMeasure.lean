-- Prove2me | solution 1 for Kyprianou.Ch01.gammaLevyMeasure_isLevyMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:18:24.709195+00:00
-- url     : https://prove2.me/submissions/46f87033-d8c5-4f10-b6d6-d40054df4ef5

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem gammaLevyMeasure_isLevyMeasure_aux
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    IsLevyMeasure (gammaLevyMeasure alpha beta) := by
  refine ⟨gammaLevyMeasure_zero alpha beta, ?_⟩
  have hExp : IntegrableOn
      (fun x : ℝ => beta * Real.exp (-alpha * x)) (Ioi (0 : ℝ)) := by
    have he := integrableOn_exp_mul_Ioi (a := -alpha) (by linarith) 0
    change Integrable (fun x : ℝ => beta * Real.exp (-alpha * x))
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [neg_mul] using he.const_mul beta
  have hExpFinite :
      (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (beta * Real.exp (-alpha * x))) < ⊤ := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => beta * Real.exp (-alpha * x))
        (volume.restrict (Ioi (0 : ℝ))) := by fun_prop
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun x : ℝ => beta * Real.exp (-alpha * x)) :=
      Filter.Eventually.of_forall (fun x => mul_nonneg hb.le (Real.exp_pos _).le)
    exact (lintegral_ofReal_ne_top_iff_integrable hm hnonneg).2 hExp |>.lt_top
  have hdenMeas : Measurable
      (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-alpha * x) / x)) := by fun_prop
  have hmeasure : (∫⁻ x,
      ENNReal.ofReal (min 1 (x ^ 2)) ∂(gammaLevyMeasure alpha beta)) =
      ∫⁻ x in Ioi (0 : ℝ),
       ENNReal.ofReal (beta * Real.exp (-alpha * x) / x) *
         ENNReal.ofReal (min 1 (x ^ 2)) := by
    unfold gammaLevyMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ hdenMeas
      (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))))]
    rfl
  rw [hmeasure]
  apply lt_of_le_of_lt _ hExpFinite
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hx
  have hmin : min (1 : ℝ) (x ^ 2) ≤ x := by
    rcases le_total x 1 with h | h
    · exact (min_le_right _ _).trans (by
        nlinarith [mul_nonneg (sub_nonneg.mpr h) hxpos.le])
    · exact (min_le_left _ _).trans h
  have hnonneg : 0 ≤ beta * Real.exp (-alpha * x) :=
    mul_nonneg hb.le (Real.exp_pos _).le
  have hdiv : (beta * Real.exp (-alpha * x) / x) *
      min 1 (x ^ 2) ≤ beta * Real.exp (-alpha * x) := by
    have hh := mul_le_mul_of_nonneg_left hmin hnonneg
    calc
      _ = (beta * Real.exp (-alpha * x) * min 1 (x ^ 2)) / x := by ring
      _ ≤ beta * Real.exp (-alpha * x) :=
        (div_le_iff₀ hxpos).2 (by nlinarith [hh])
  calc
    ENNReal.ofReal (beta * Real.exp (-alpha * x) / x) *
        ENNReal.ofReal (min 1 (x ^ 2)) =
      ENNReal.ofReal ((beta * Real.exp (-alpha * x) / x) *
        min 1 (x ^ 2)) :=
          (ENNReal.ofReal_mul (div_nonneg hnonneg hxpos.le)).symm
    _ ≤ ENNReal.ofReal (beta * Real.exp (-alpha * x)) :=
      ENNReal.ofReal_le_ofReal hdiv


theorem solution
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    IsLevyMeasure (gammaLevyMeasure alpha beta) := by
  exact gammaLevyMeasure_isLevyMeasure_aux alpha beta ha hb
