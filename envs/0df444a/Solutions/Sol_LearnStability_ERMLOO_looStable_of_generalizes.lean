-- Prove2me | solution 1 for LearnStability.ERMLOO.looStable_of_generalizes
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:56:44.28665+00:00
-- url     : https://prove2.me/submissions/b46c7c1f-cf70-4380-ae5c-84e39349c3bf

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

set_option autoImplicit false

open MeasureTheory

namespace P2M877e6e8c

open LearnStability.ERMLOO

lemma integrable_of_abs_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

lemma empRisk_abs_le {H Z : Type*} [MeasurableSpace Z] (f : H → Z → ℝ) (B : ℝ)
    (hf : StandingAssumptions f B) {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (h : H) :
    |empRisk f S h| ≤ B := by
  unfold empRisk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => hf.bounded h (S i)
    _ = B * m := by simp [mul_comm]

lemma empRisk_ge {H Z : Type*} [MeasurableSpace Z] (f : H → Z → ℝ) (B : ℝ)
    (hf : StandingAssumptions f B) {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (h : H) :
    -B ≤ empRisk f S h :=
  (abs_le.mp (empRisk_abs_le f B hf hm S h)).1

lemma erm_sum_le {H Z : Type*} [MeasurableSpace Z] (f : H → Z → ℝ) (B : ℝ)
    (hf : StandingAssumptions f B) (A : Rule H Z) (hERM : IsERMRule f A)
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (h : H) :
    ∑ i, f (A m S) (S i) ≤ ∑ i, f h (S i) := by
  have h1 : empRisk f S (A m S) ≤ empRisk f S h := by
    rw [hERM m hm S]
    exact ciInf_le ⟨-B, by rintro _ ⟨h', rfl⟩; exact empRisk_ge f B hf hm S h'⟩ h
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  unfold empRisk at h1
  exact (div_le_div_iff_of_pos_right hmpos).mp h1

lemma sum_removeNth {Z : Type*} {n : ℕ} (g : Z → ℝ) (S : Fin (n + 1) → Z) (i : Fin (n + 1)) :
    ∑ k, g (Fin.removeNth i S k) = ∑ j, g (S j) - g (S i) := by
  rw [Fin.sum_univ_succAbove (fun j => g (S j)) i]
  simp [Fin.removeNth]

lemma pointwise_key {H Z : Type*} [MeasurableSpace Z] (f : H → Z → ℝ) (B : ℝ)
    (hf : StandingAssumptions f B) (A : Rule H Z) (hERM : IsERMRule f A)
    (n : ℕ) (hn : 1 ≤ n) (S : Fin (n + 1) → Z) :
    ∑ i, |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)| ≤
      ∑ i, (f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) := by
  set a := A (n + 1) S with ha
  set T : H → ℝ := fun h => ∑ j, f h (S j) with hT
  have hA1 : ∀ h, T a ≤ T h := fun h => erm_sum_le f B hf A hERM (by omega) S h
  have hA2 : ∀ (i : Fin (n + 1)) h, T (A n (Fin.removeNth i S)) - f (A n (Fin.removeNth i S)) (S i)
      ≤ T h - f h (S i) := by
    intro i h
    have := erm_sum_le f B hf A hERM hn (Fin.removeNth i S) h
    rwa [sum_removeNth (f (A n (Fin.removeNth i S))) S i, sum_removeNth (f h) S i] at this
  have hemp : ∀ i : Fin (n + 1), empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S)) =
      (T (A n (Fin.removeNth i S)) - f (A n (Fin.removeNth i S)) (S i)) / n := by
    intro i
    unfold empRisk
    rw [sum_removeNth]
  have habs : ∀ i : Fin (n + 1), |f (A n (Fin.removeNth i S)) (S i) - f a (S i)| =
      f (A n (Fin.removeNth i S)) (S i) - f a (S i) := by
    intro i
    apply abs_of_nonneg
    have := hA2 i a
    have := hA1 (A n (Fin.removeNth i S))
    linarith
  simp_rw [habs, hemp]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i : Fin (n + 1), (T (A n (Fin.removeNth i S)) - f (A n (Fin.removeNth i S)) (S i)) / n
      ≤ ∑ i : Fin (n + 1), (T a - f a (S i)) / n :=
    Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hA2 i a) hnpos.le
  have hTa : ∑ i : Fin (n + 1), (T a - f a (S i)) / n = T a := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : ∑ i : Fin (n + 1), f a (S i) = T a := rfl
    rw [this]
    field_simp
    push_cast
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have : ∑ i : Fin (n + 1), f a (S i) = T a := rfl
  rw [this]
  linarith

instance sampleLaw_isProb {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) : IsProbabilityMeasure (sampleLaw D m) := by
  unfold sampleLaw; infer_instance

end P2M877e6e8c

open MeasureTheory LearnStability.ERMLOO in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (hERM : IsERMRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εgen : ℕ → ℝ)
    (hgen : Generalizes f A D εgen) :
    LOOStable f A D (fun m => εgen (m - 1)) := by
  intro n hn
  show _ ≤ εgen n
  have hB : ∀ h z, |f h z| ≤ B := hf.bounded
  have hmE : ∀ (m : ℕ) {X : Type _} [MeasurableSpace X] (q : X → (Fin m → Z)), Measurable q →
      Measurable (fun x => empRisk f (q x) (A m (q x))) := by
    intro m X _ q hq
    unfold empRisk
    exact (Finset.measurable_sum _ fun j _ =>
      (hA m).comp (hq.prodMk ((measurable_pi_apply j).comp hq))).div_const _
  have hrem : ∀ i : Fin (n + 1), Measurable (fun S : Fin (n + 1) → Z => Fin.removeNth i S) :=
    fun i => measurable_pi_lambda _ fun j => measurable_pi_apply _
  -- integrability of the two families of integrands
  have hdint : ∀ i : Fin (n + 1), Integrable (fun S : Fin (n + 1) → Z =>
      |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|) (sampleLaw D (n + 1)) := by
    intro i
    refine P2M877e6e8c.integrable_of_abs_le _ _ ?_ (B + B) ?_
    · exact (((hA n).comp ((hrem i).prodMk (measurable_pi_apply i))).sub
        ((hA (n + 1)).comp (measurable_id.prodMk (measurable_pi_apply i)))).abs
    · intro S
      rw [abs_abs]
      exact (abs_sub _ _).trans (add_le_add (hB _ _) (hB _ _))
  have hgint : ∀ i : Fin (n + 1), Integrable (fun S : Fin (n + 1) → Z =>
      f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) (sampleLaw D (n + 1)) := by
    intro i
    refine P2M877e6e8c.integrable_of_abs_le _ _ ?_ (B + B) ?_
    · exact ((hA n).comp ((hrem i).prodMk (measurable_pi_apply i))).sub (hmE n _ (hrem i))
    · intro S
      exact (abs_sub _ _).trans (add_le_add (hB _ _) (P2M877e6e8c.empRisk_abs_le f B hf hn _ _))
  -- each leave-one-out term is bounded by the generalization rate
  have hstep : ∀ i : Fin (n + 1), ∫ S, (f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) ∂(sampleLaw D (n + 1))
        ≤ εgen n := by
    intro i
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) i
    set φ : Z × (Fin n → Z) → ℝ := fun p => f (A n p.2) p.1 - empRisk f p.2 (A n p.2) with hφ
    have hφm : Measurable φ :=
      ((hA n).comp (measurable_snd.prodMk measurable_fst)).sub (hmE n _ measurable_snd)
    have hφint : Integrable φ (D.prod (sampleLaw D n)) := by
      refine P2M877e6e8c.integrable_of_abs_le _ _ hφm (B + B) ?_
      intro p
      exact (abs_sub _ _).trans (add_le_add (hB _ _) (P2M877e6e8c.empRisk_abs_le f B hf hn _ _))
    have h1 : ∫ S, (f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) ∂(sampleLaw D (n + 1))
        = ∫ p, φ p ∂(D.prod (sampleLaw D n)) := by
      exact hmp.integral_comp' φ
    have h3 : ∀ T : Fin n → Z, ∫ z, φ (z, T) ∂D = risk f D (A n T) - empRisk f T (A n T) := by
      intro T
      simp only [hφ]
      have hi : Integrable (fun z => f (A n T) z) D :=
        P2M877e6e8c.integrable_of_abs_le _ _ (hf.measurable _) B (fun z => hB _ _)
      rw [integral_sub hi (integrable_const _), integral_const]
      simp [risk]
    rw [h1, integral_prod_symm φ hφint]
    simp_rw [h3]
    calc _ ≤ |∫ T, (risk f D (A n T) - empRisk f T (A n T)) ∂(sampleLaw D n)| := le_abs_self _
      _ ≤ ∫ T, |risk f D (A n T) - empRisk f T (A n T)| ∂(sampleLaw D n) :=
          abs_integral_le_integral_abs
      _ ≤ εgen n := hgen n hn
  have hsum : ∑ i : Fin (n + 1), ∫ S, |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
      ∂(sampleLaw D (n + 1)) ≤ (n + 1) * εgen n := by
    calc _ = ∫ S, ∑ i : Fin (n + 1), |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
          ∂(sampleLaw D (n + 1)) := (integral_finsetSum _ fun i _ => hdint i).symm
      _ ≤ ∫ S, ∑ i : Fin (n + 1), (f (A n (Fin.removeNth i S)) (S i)
          - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) ∂(sampleLaw D (n + 1)) :=
          integral_mono (integrable_finsetSum _ fun i _ => hdint i)
            (integrable_finsetSum _ fun i _ => hgint i)
            (fun S => P2M877e6e8c.pointwise_key f B hf A hERM n hn S)
      _ = ∑ i : Fin (n + 1), ∫ S, (f (A n (Fin.removeNth i S)) (S i)
          - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) ∂(sampleLaw D (n + 1)) :=
          integral_finsetSum _ fun i _ => hgint i
      _ ≤ ∑ _i : Fin (n + 1), εgen n := Finset.sum_le_sum fun i _ => hstep i
      _ = (n + 1) * εgen n := by simp
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_iff₀ hpos]
  linarith
