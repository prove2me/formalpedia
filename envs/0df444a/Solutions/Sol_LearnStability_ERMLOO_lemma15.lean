-- Prove2me | solution 1 for LearnStability.ERMLOO.lemma15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:44:05.77157+00:00
-- url     : https://prove2.me/submissions/417d4e06-12ed-40c9-83ec-7c301c2077b8

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

set_option autoImplicit false

open MeasureTheory LearnStability.ERMLOO in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εoag : ℕ → ℝ)
    (hAERM : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) :
    Consistent f A D (fun m => εoag m + εerm m) := by
  intro m hm
  have : IsProbabilityMeasure (sampleLaw D m) := by
    unfold sampleLaw; infer_instance
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hrisk : ∀ h, |risk f D h| ≤ B := by
    intro h
    have := norm_integral_le_of_norm_le_const (μ := D) (f := f h) (C := B)
      (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hf.bounded h z))
    simpa [risk, Real.norm_eq_abs] using this
  have hemp : ∀ (S : Fin m → Z) h, |empRisk f S h| ≤ B := by
    intro S h
    unfold empRisk
    rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
    calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum (fun i _ => hf.bounded h (S i))
      _ = B * m := by simp [mul_comm]
  have hermle : ∀ (S : Fin m → Z) h, ermValue f S ≤ empRisk f S h := fun S h =>
    ciInf_le ⟨-B, by rintro _ ⟨h', rfl⟩; exact (abs_le.mp (hemp S h')).1⟩ h
  obtain ⟨h0⟩ := ‹Nonempty H›
  have herm_abs : ∀ S : Fin m → Z, |ermValue f S| ≤ B := by
    intro S
    rw [abs_le]; constructor
    · exact le_ciInf (fun h => (abs_le.mp (hemp S h)).1)
    · exact (hermle S h0).trans (abs_le.mp (hemp S h0)).2
  have mrisk : StronglyMeasurable (fun S : Fin m → Z => risk f D (A m S)) := by
    have := (hA m).stronglyMeasurable.integral_prod_right' (ν := D)
    simpa [risk] using this
  have memp : Measurable (fun S : Fin m → Z => empRisk f S (A m S)) := by
    unfold empRisk
    refine Measurable.div_const ?_ _
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (hA m).comp (measurable_id.prodMk (measurable_pi_apply i))
  have merm : Measurable (fun S : Fin m → Z => ermValue f S) := herm m
  have iR : Integrable (fun S : Fin m → Z => risk f D (A m S)) (sampleLaw D m) :=
    Integrable.of_bound mrisk.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun S => by rw [Real.norm_eq_abs]; exact hrisk _)
  have iE : Integrable (fun S : Fin m → Z => empRisk f S (A m S)) (sampleLaw D m) :=
    Integrable.of_bound memp.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun S => by rw [Real.norm_eq_abs]; exact hemp _ _)
  have iM : Integrable (fun S : Fin m → Z => ermValue f S) (sampleLaw D m) :=
    Integrable.of_bound merm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun S => by rw [Real.norm_eq_abs]; exact herm_abs _)
  have ifh : ∀ h, Integrable (f h) D := fun h =>
    Integrable.of_bound (hf.measurable h).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hf.bounded h z)
  -- expected empirical risk of a fixed hypothesis equals its risk
  have hEh : ∀ h, ∫ S, empRisk f S h ∂(sampleLaw D m) = risk f D h := by
    intro h
    unfold empRisk sampleLaw
    rw [integral_div, integral_finsetSum]
    · have : ∀ i ∈ (Finset.univ : Finset (Fin m)),
          ∫ S : Fin m → Z, f h (S i) ∂(Measure.pi fun _ : Fin m => D) = risk f D h := by
        intro i _
        rw [integral_comp_eval (μ := fun _ : Fin m => D) (f := f h)
          (hf.measurable h).aestronglyMeasurable]
        rfl
      rw [Finset.sum_congr rfl this]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro i _
      exact integrable_comp_eval (μ := fun _ : Fin m => D) (ifh h)
  have iEh : ∀ h, Integrable (fun S : Fin m → Z => empRisk f S h) (sampleLaw D m) := by
    intro h
    refine Integrable.of_bound ?_ B
      (Filter.Eventually.of_forall fun S => by rw [Real.norm_eq_abs]; exact hemp _ _)
    unfold empRisk
    refine (Measurable.div_const ?_ _).aestronglyMeasurable
    exact Finset.measurable_sum _ (fun i _ => (hf.measurable h).comp (measurable_pi_apply i))
  have hErm : ∫ S, ermValue f S ∂(sampleLaw D m) ≤ optRisk f D := by
    unfold optRisk
    refine le_ciInf (fun h => ?_)
    rw [← hEh h]
    exact integral_mono iM (iEh h) (fun S => hermle S h)
  have e1 : ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) =
      ∫ S, risk f D (A m S) ∂(sampleLaw D m) - optRisk f D := by
    rw [integral_sub iR (integrable_const _)]
    simp
  have e2 : ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(sampleLaw D m) =
      ∫ S, risk f D (A m S) ∂(sampleLaw D m) - ∫ S, empRisk f S (A m S) ∂(sampleLaw D m) :=
    integral_sub iR iE
  have e3 : ∫ S, (empRisk f S (A m S) - ermValue f S) ∂(sampleLaw D m) =
      ∫ S, empRisk f S (A m S) ∂(sampleLaw D m) - ∫ S, ermValue f S ∂(sampleLaw D m) :=
    integral_sub iE iM
  have h1 := hAERM m hm
  have h2 := le_abs_self (∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(sampleLaw D m))
  have h3 := hoag m hm
  show _ ≤ εoag m + εerm m
  rw [e1]
  rw [e3] at h1
  rw [e2] at h2 h3
  linarith
