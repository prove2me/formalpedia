-- Prove2me | solution 1 for LearnStability.Characterization.lemma15_aerm_onAverage_consistent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:40:23.967765+00:00
-- url     : https://prove2.me/submissions/904f7607-3979-4cd5-9a25-88aa251fb85c

import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties

open MeasureTheory Finset
open LearnStability.Characterization
namespace CLearnBounds
variable {H Z : Type*} [MeasurableSpace Z]

theorem emp_bound (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (h : H) : |empRisk f S h| ≤ B := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold empRisk
  rw [abs_div,show |(m : ℝ)|=m from abs_of_nonneg (le_of_lt hm0)]
  calc
    _ ≤ (∑ i,|f h (S i)|)/(m : ℝ) := div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (le_of_lt hm0)
    _ ≤ (∑ _ : Fin m,B)/(m : ℝ) := by gcongr with i;exact hP.bounded h (S i)
    _=B := by simp [ne_of_gt hm0]

theorem risk_bound (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (D : Measure Z) [IsProbabilityMeasure D] (h : H) : |risk f D h| ≤ B := by
  have hh:=norm_integral_le_of_norm_le_const (μ:=D) (f:=f h)
    (Filter.Eventually.of_forall (fun z=>by simpa only [Real.norm_eq_abs] using hP.bounded h z))
  simpa [risk,Real.norm_eq_abs] using hh

theorem erm_bound [Nonempty H] (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) : |ermValue f S| ≤ B := by
  classical
  have hb : BddBelow (Set.range (empRisk f S)) := by
    refine ⟨-B,?_⟩
    rintro r ⟨h,rfl⟩
    exact (abs_le.mp (emp_bound f B hP hm S h)).1
  apply abs_le.mpr
  constructor
  · exact le_ciInf (fun h=>(abs_le.mp (emp_bound f B hP hm S h)).1)
  · exact (ciInf_le hb (Classical.arbitrary H)).trans (abs_le.mp (emp_bound f B hP hm S _)).2

theorem emp_meas (f : H → Z → ℝ) (A : Rule H Z) (hA : MeasurableRule f A) (m : ℕ) :
    Measurable (fun S : Fin m → Z=>empRisk f S (A m S)) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _=>(hA m).comp (measurable_id.prodMk (measurable_pi_apply i)))

theorem integrable_three [Nonempty H] (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun S : Fin m → Z=>empRisk f S (A m S)) (sampleLaw D m) ∧
    Integrable (fun S : Fin m → Z=>risk f D (A m S)) (sampleLaw D m) ∧
    Integrable (fun S : Fin m → Z=>ermValue f S) (sampleLaw D m) := by
  haveI : IsProbabilityMeasure (sampleLaw D m) := by unfold sampleLaw;infer_instance
  refine ⟨?_,?_,?_⟩
  · apply Integrable.of_bound (emp_meas f A hA m).aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun S=>by simpa only [Real.norm_eq_abs] using emp_bound f B hP hm S (A m S))
  · apply Integrable.of_bound (hA m).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun S=>by simpa only [Real.norm_eq_abs,risk] using risk_bound f B hP D (A m S))
  · apply Integrable.of_bound (hP.measurable_ermValue m).aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun S=>by simpa only [Real.norm_eq_abs] using erm_bound f B hP hm S)

end CLearnBounds

private lemma expectation_emp {H Z : Type*} [MeasurableSpace Z]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (D : Measure Z) [IsProbabilityMeasure D] (h : H) (m : ℕ) (hm : 1 ≤ m) :
    (∫ S, empRisk f S h ∂sampleLaw D m) = risk f D h := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  haveI : IsProbabilityMeasure (sampleLaw D m) := by unfold sampleLaw; infer_instance
  have hi (i : Fin m) : Integrable (fun S : Fin m → Z => f h (S i)) (sampleLaw D m) := by
    apply Integrable.of_bound ((hP.measurable h).comp (measurable_pi_apply i)).aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun S => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hP.bounded h (S i))
  have he (i : Fin m) : (∫ S, f h (S i) ∂sampleLaw D m) = risk f D h := by
    have hp := measurePreserving_eval (fun _ : Fin m => D) i
    change _ = ∫ z, f h z ∂D
    calc
      _ = ∫ z, f h z ∂(Measure.map (Function.eval i) (Measure.pi fun _ : Fin m => D)) :=
        (integral_map hp.measurable.aemeasurable (hP.measurable h).aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]
  unfold empRisk
  rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  simp [hm0]

theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εoag : ℕ → ℝ)
    (haerm : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) :
    Consistent f A D (fun m => εoag m + εerm m) := by
  classical
  intro m hm
  haveI : IsProbabilityMeasure (sampleLaw D m) := by unfold sampleLaw; infer_instance
  obtain ⟨hE,hR,hT⟩ := CLearnBounds.integrable_three f B hP A hA D m hm
  have hmin : (∫ S, ermValue f S ∂sampleLaw D m) ≤ optRisk f D := by
    apply le_ciInf
    intro h
    rw [← expectation_emp f B hP D h m hm]
    apply integral_mono hT
    · refine Integrable.of_bound ?_ B ?_
      · apply Measurable.aestronglyMeasurable
        exact (Finset.measurable_sum _ (fun i _ => (hP.measurable h).comp (measurable_pi_apply i))).div_const _
      · exact Filter.Eventually.of_forall (fun S => by simpa only [Real.norm_eq_abs] using CLearnBounds.emp_bound f B hP hm S h)
    · intro S
      apply ciInf_le
      refine ⟨-B, ?_⟩
      rintro r ⟨h',rfl⟩
      exact (abs_le.mp (CLearnBounds.emp_bound f B hP hm S h')).1
  have hg := (le_abs_self (∫ S, risk f D (A m S) - empRisk f S (A m S) ∂sampleLaw D m)).trans (hoag m hm)
  have he := haerm m hm
  rw [integral_sub hR hE] at hg
  rw [integral_sub hE hT] at he
  rw [integral_sub hR (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  linarith
