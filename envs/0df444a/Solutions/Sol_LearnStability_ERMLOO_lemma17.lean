-- Prove2me | solution 1 for LearnStability.ERMLOO.lemma17
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:58:11.401971+00:00
-- url     : https://prove2.me/submissions/6cad9b6a-be55-4fe6-a2ef-9016f943f76f

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

set_option autoImplicit false

open MeasureTheory LearnStability.ERMLOO in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εemp εerm εcons : ℕ → ℝ)
    (h12 : ∀ m : ℕ, 1 ≤ m → ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤ εemp m)
    (hAERM : IsAERM f A D εerm) (hcons : Consistent f A D εcons) :
    Generalizes f A D (fun m => εemp m + εerm m + εcons m) := by
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
  have hoptle : ∀ h, optRisk f D ≤ risk f D h := fun h =>
    ciInf_le ⟨-B, by rintro _ ⟨h', rfl⟩; exact (abs_le.mp (hrisk h')).1⟩ h
  have hermle : ∀ (S : Fin m → Z) h, ermValue f S ≤ empRisk f S h := fun S h =>
    ciInf_le ⟨-B, by rintro _ ⟨h', rfl⟩; exact (abs_le.mp (hemp S h')).1⟩ h
  obtain ⟨h0⟩ := ‹Nonempty H›
  have hopt_abs : |optRisk f D| ≤ B := by
    rw [abs_le]; constructor
    · exact le_ciInf (fun h => (abs_le.mp (hrisk h)).1)
    · exact (hoptle h0).trans (abs_le.mp (hrisk h0)).2
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
  have two : ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → ‖x - y‖ ≤ 2 * B := by
    intro x y hx hy
    rw [Real.norm_eq_abs, abs_le]
    have := abs_le.mp hx; have := abs_le.mp hy
    constructor <;> linarith
  have iR : Integrable (fun S : Fin m → Z => risk f D (A m S) - optRisk f D) (sampleLaw D m) :=
    Integrable.of_bound (mrisk.measurable.sub_const _).aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun S => two _ _ (hrisk _) hopt_abs)
  have iE : Integrable (fun S : Fin m → Z => empRisk f S (A m S) - ermValue f S)
      (sampleLaw D m) :=
    Integrable.of_bound (memp.sub merm).aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun S => two _ _ (hemp _ _) (herm_abs S))
  have iC : Integrable (fun S : Fin m → Z => |ermValue f S - optRisk f D|) (sampleLaw D m) :=
    Integrable.of_bound ((merm.sub_const _).abs).aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun S => by
        rw [Real.norm_eq_abs, abs_abs]
        have := two _ _ (herm_abs S) hopt_abs
        rwa [Real.norm_eq_abs] at this)
  have iG : Integrable (fun S : Fin m → Z => |risk f D (A m S) - empRisk f S (A m S)|)
      (sampleLaw D m) :=
    Integrable.of_bound ((mrisk.measurable.sub memp).abs).aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun S => by
        rw [Real.norm_eq_abs, abs_abs]
        have := two _ _ (hrisk (A m S)) (hemp S (A m S))
        rwa [Real.norm_eq_abs] at this)
  have hpt : ∀ S : Fin m → Z, |risk f D (A m S) - empRisk f S (A m S)| ≤
      ((risk f D (A m S) - optRisk f D) + |ermValue f S - optRisk f D|) +
        (empRisk f S (A m S) - ermValue f S) := by
    intro S
    have h1 := hoptle (A m S)
    have h2 := hermle S (A m S)
    have h3 := le_abs_self (ermValue f S - optRisk f D)
    have h4 := neg_abs_le (ermValue f S - optRisk f D)
    rw [abs_le]; constructor <;> linarith
  have hint : ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(sampleLaw D m) ≤
      ∫ S, (((risk f D (A m S) - optRisk f D) + |ermValue f S - optRisk f D|) +
        (empRisk f S (A m S) - ermValue f S)) ∂(sampleLaw D m) :=
    integral_mono iG ((iR.add iC).add iE) hpt
  have e1 : ∫ S, (((risk f D (A m S) - optRisk f D) + |ermValue f S - optRisk f D|) +
        (empRisk f S (A m S) - ermValue f S)) ∂(sampleLaw D m) =
      ∫ S, ((risk f D (A m S) - optRisk f D) + |ermValue f S - optRisk f D|) ∂(sampleLaw D m) +
        ∫ S, (empRisk f S (A m S) - ermValue f S) ∂(sampleLaw D m) :=
    integral_add (iR.add iC) iE
  have e2 : ∫ S, ((risk f D (A m S) - optRisk f D) + |ermValue f S - optRisk f D|)
        ∂(sampleLaw D m) =
      ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) +
        ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) :=
    integral_add iR iC
  have := h12 m hm
  have := hAERM m hm
  have := hcons m hm
  show _ ≤ εemp m + εerm m + εcons m
  linarith
