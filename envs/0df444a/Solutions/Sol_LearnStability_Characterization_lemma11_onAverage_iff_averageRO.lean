-- Prove2me | solution 1 for LearnStability.Characterization.lemma11_onAverage_iff_averageRO
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:14:15.491888+00:00
-- url     : https://prove2.me/submissions/289fdaa4-897e-4435-8a1a-5f9b1d239330

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

set_option autoImplicit false

open MeasureTheory

namespace LearnStability.Characterization.L11Aux

open LearnStability.Characterization

universe u v

lemma mp_update {Z : Type v} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Z) × (Fin m → Z) => Function.update p.1 i (p.2 i))
      ((sampleLaw D m).prod (sampleLaw D m)) (sampleLaw D m) := by
  have he := (measurePreserving_arrowProdEquivProdArrow Z Z (Fin m)
    (fun _ => D) (fun _ => D)).symm
  have hψ : MeasurePreserving (fun (q : Fin m → Z × Z) (j : Fin m) =>
      (if j = i then Prod.snd else Prod.fst : Z × Z → Z) (q j))
      (Measure.pi fun _ => D.prod D) (Measure.pi fun _ => D) := by
    refine measurePreserving_pi _ _ (fun j => ?_)
    split_ifs
    · exact measurePreserving_snd
    · exact measurePreserving_fst
  have hc := hψ.comp he
  unfold sampleLaw
  convert hc using 1
  funext p
  funext j
  simp only [Function.comp, Function.update_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

lemma key {H : Type u} {Z : Type v} [MeasurableSpace Z]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 1 ≤ m) :
    (∑ i, ∫ p, (f (A m (Function.update p.1 i (p.2 i))) (p.2 i) - f (A m p.1) (p.2 i))
        ∂((sampleLaw D m).prod (sampleLaw D m))) / m
      = - ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(sampleLaw D m) := by
  set μ := sampleLaw D m with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; unfold sampleLaw; infer_instance
  have hh : Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2) := hA m
  have hbd : ∀ h z, ‖f h z‖ ≤ B := fun h z => by rw [Real.norm_eq_abs]; exact hP.bounded h z
  have hg : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f (A m S) (S i)) := fun i =>
    hh.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hr : Measurable (fun S : Fin m → Z => risk f D (A m S)) := by
    unfold risk
    exact (hh.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hgI : ∀ i : Fin m, Integrable (fun S : Fin m → Z => f (A m S) (S i)) μ := fun i =>
    Integrable.of_bound (hg i).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun S => hbd _ _)
  have hrI : Integrable (fun S : Fin m → Z => risk f D (A m S)) μ := by
    refine Integrable.of_bound hr.aestronglyMeasurable B (Filter.Eventually.of_forall fun S => ?_)
    unfold risk
    calc ‖∫ z, f (A m S) z ∂D‖ ≤ ∫ _z, B ∂D :=
          norm_integral_le_of_norm_le (integrable_const B)
            (Filter.Eventually.of_forall fun z => hbd _ _)
      _ = B := by simp
  have hΦm : ∀ i : Fin m, Measurable
      (fun p : (Fin m → Z) × (Fin m → Z) => f (A m (Function.update p.1 i (p.2 i))) (p.2 i)) := by
    intro i
    have : (fun p : (Fin m → Z) × (Fin m → Z) => f (A m (Function.update p.1 i (p.2 i))) (p.2 i))
        = (fun S : Fin m → Z => f (A m S) (S i)) ∘
          (fun p : (Fin m → Z) × (Fin m → Z) => Function.update p.1 i (p.2 i)) := by
      funext p; simp
    rw [this]
    exact (hg i).comp (mp_update D m i).measurable
  have hχm : ∀ i : Fin m, Measurable
      (fun p : (Fin m → Z) × (Fin m → Z) => f (A m p.1) (p.2 i)) := fun i =>
    hh.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hT1 : ∀ i : Fin m, ∫ p, f (A m (Function.update p.1 i (p.2 i))) (p.2 i) ∂(μ.prod μ)
      = ∫ S, f (A m S) (S i) ∂μ := by
    intro i
    have hΦ : MeasurePreserving
        (fun p : (Fin m → Z) × (Fin m → Z) => Function.update p.1 i (p.2 i)) (μ.prod μ) μ :=
      mp_update D m i
    have e := integral_map (μ := μ.prod μ) hΦ.measurable.aemeasurable
      (f := fun S : Fin m → Z => f (A m S) (S i))
      (by rw [hΦ.map_eq]; exact (hg i).aestronglyMeasurable)
    rw [hΦ.map_eq] at e
    simp only [Function.update_self] at e
    exact e.symm
  have hT2 : ∀ i : Fin m, ∫ p, f (A m p.1) (p.2 i) ∂(μ.prod μ)
      = ∫ S, risk f D (A m S) ∂μ := by
    intro i
    have hev : MeasurePreserving (fun S' : Fin m → Z => S' i) μ D := by
      rw [hμ]; unfold sampleLaw; exact measurePreserving_eval (fun _ => D) i
    have hχ : MeasurePreserving (Prod.map id (fun S' : Fin m → Z => S' i)) (μ.prod μ) (μ.prod D) :=
      (MeasurePreserving.id μ).prod hev
    have e := integral_map (μ := μ.prod μ) hχ.measurable.aemeasurable
      (f := fun p : (Fin m → Z) × Z => f (A m p.1) p.2)
      (by rw [hχ.map_eq]; exact hh.aestronglyMeasurable)
    rw [hχ.map_eq] at e
    rw [show (∫ p, f (A m p.1) (p.2 i) ∂(μ.prod μ))
        = ∫ y, f (A m y.1) y.2 ∂(μ.prod D) from e.symm]
    rw [integral_prod _ (Integrable.of_bound hh.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => hbd _ _))]
    rfl
  have hI1 : ∀ i : Fin m, Integrable
      (fun p : (Fin m → Z) × (Fin m → Z) => f (A m (Function.update p.1 i (p.2 i))) (p.2 i))
      (μ.prod μ) := fun i =>
    Integrable.of_bound (hΦm i).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => hbd _ _)
  have hI2 : ∀ i : Fin m, Integrable
      (fun p : (Fin m → Z) × (Fin m → Z) => f (A m p.1) (p.2 i)) (μ.prod μ) := fun i =>
    Integrable.of_bound (hχm i).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => hbd _ _)
  have hsum : ∀ i : Fin m,
      ∫ p, (f (A m (Function.update p.1 i (p.2 i))) (p.2 i) - f (A m p.1) (p.2 i)) ∂(μ.prod μ)
        = ∫ S, f (A m S) (S i) ∂μ - ∫ S, risk f D (A m S) ∂μ := by
    intro i
    rw [integral_sub (hI1 i) (hI2 i), hT1 i, hT2 i]
  have hemp : ∫ S, empRisk f S (A m S) ∂μ = (∑ i, ∫ S, f (A m S) (S i) ∂μ) / m := by
    unfold empRisk
    rw [integral_div, integral_finsetSum _ (fun i _ => hgI i)]
  have hempI : Integrable (fun S : Fin m → Z => empRisk f S (A m S)) μ := by
    unfold empRisk
    exact (integrable_finsetSum _ (fun i _ => hgI i)).div_const _
  rw [Finset.sum_congr rfl (fun i _ => hsum i), integral_sub hrI hempI, hemp,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  field_simp
  ring

end LearnStability.Characterization.L11Aux

open MeasureTheory LearnStability.Characterization in
theorem solution {H Z : Type*} [MeasurableSpace Z]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (ε : ℕ → ℝ) :
    (OnAverageGeneralizes f A D ε → AverageROStable f A D ε) ∧
      (AverageROStable f A D ε → OnAverageGeneralizes f A D ε) := by
  constructor
  · intro h m hm
    rw [L11Aux.key f B hP A hA D m hm, abs_neg]
    exact h m hm
  · intro h m hm
    have := h m hm
    rwa [L11Aux.key f B hP A hA D m hm, abs_neg] at this
