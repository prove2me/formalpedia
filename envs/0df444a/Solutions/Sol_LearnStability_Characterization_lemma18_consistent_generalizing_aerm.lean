-- Prove2me | solution 1 for LearnStability.Characterization.lemma18_consistent_generalizing_aerm
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:40:18.657511+00:00
-- url     : https://prove2.me/submissions/42ea87ef-9011-47b1-8b10-b76f1b5ecbfe

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

theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εemp εcons εgen : ℕ → ℝ)
    (h12 : ∀ m : ℕ, 1 ≤ m →
      ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤ εemp m)
    (hcons : Consistent f A D εcons) (hgen : Generalizes f A D εgen) :
    IsAERM f A D (fun m => εemp m + εgen m + εcons m) := by
  intro m hm
  haveI : IsProbabilityMeasure (sampleLaw D m) := by unfold sampleLaw;infer_instance
  obtain ⟨hE,hR,hT⟩:=CLearnBounds.integrable_three f B hP A hA D m hm
  have h1 := (hT.sub (integrable_const (optRisk f D))).norm
  have h2 := (hR.sub hE).norm
  have h3 := hR.sub (integrable_const (optRisk f D))
  change Integrable (fun S=>|ermValue f S-optRisk f D|) (sampleLaw D m) at h1
  change Integrable (fun S=>|risk f D (A m S)-empRisk f S (A m S)|) (sampleLaw D m) at h2
  change Integrable (fun S=>risk f D (A m S)-optRisk f D) (sampleLaw D m) at h3
  have hbound :
      (∫ S,empRisk f S (A m S)-ermValue f S ∂sampleLaw D m) ≤
        (∫ S,|ermValue f S-optRisk f D| ∂sampleLaw D m)+
        (∫ S,|risk f D (A m S)-empRisk f S (A m S)| ∂sampleLaw D m)+
        (∫ S,risk f D (A m S)-optRisk f D ∂sampleLaw D m) := by
    rw [←integral_add h1 h2]
    erw [←integral_add (h1.add h2) h3]
    apply integral_mono (hE.sub hT) ((h1.add h2).add h3)
    intro S
    have ht := neg_abs_le (ermValue f S-optRisk f D)
    have hr := neg_abs_le (risk f D (A m S)-empRisk f S (A m S))
    dsimp only [Pi.add_apply,Pi.sub_apply]
    linarith
  exact hbound.trans (add_le_add (add_le_add (h12 m hm) (hgen m hm)) (hcons m hm))
