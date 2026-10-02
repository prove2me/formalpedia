-- Prove2me | solution 1 for LearnStability.ERMLOO.onAverageGeneralizes_of_looStable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:21:20.292411+00:00
-- url     : https://prove2.me/submissions/60cdc3dd-d2c4-4d48-ba18-aa3ada208acf

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

set_option autoImplicit false

open MeasureTheory

namespace LearnStability.ERMLOO.P5e295723

open LearnStability.ERMLOO

lemma sampleLaw_prob {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (k : ℕ) : IsProbabilityMeasure (sampleLaw D k) := by
  unfold sampleLaw; infer_instance

lemma integrable_bdd {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (k : ℕ) (g : (Fin k → Z) → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    Integrable g (sampleLaw D k) := by
  have := sampleLaw_prob D k
  exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

lemma meas_term {H Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X] (f : H → Z → ℝ)
    (A : Rule H Z) (hA : MeasurableRule f A) (k : ℕ) (T : X → (Fin k → Z)) (hT : Measurable T)
    (u : X → Z) (hu : Measurable u) :
    Measurable (fun S => f (A k (T S)) (u S)) :=
  (hA k).comp (hT.prodMk hu)

lemma meas_empRisk {H Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X] (f : H → Z → ℝ)
    (A : Rule H Z) (hA : MeasurableRule f A) (k : ℕ) (T : X → (Fin k → Z)) (hT : Measurable T) :
    Measurable (fun S => empRisk f (T S) (A k (T S))) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun j _ => ?_
  exact meas_term f A hA k T hT (fun S => T S j) ((measurable_pi_apply j).comp hT)

lemma abs_empRisk_le {H Z : Type*} (f : H → Z → ℝ) (B : ℝ) (hb : ∀ h z, |f h z| ≤ B)
    {k : ℕ} (hk : 0 < k) (S : Fin k → Z) (h : H) : |empRisk f S h| ≤ B := by
  unfold empRisk
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  rw [abs_div, abs_of_pos hkpos, div_le_iff₀ hkpos]
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum fun i _ => hb h (S i)
    _ = B * k := by simp [mul_comm]

lemma measurable_removeNth {Z : Type*} [MeasurableSpace Z] {n : ℕ} (i : Fin (n + 1)) :
    Measurable (fun S : Fin (n + 1) → Z => Fin.removeNth i S) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply _

lemma transfer {H Z : Type*} [MeasurableSpace Z] (f : H → Z → ℝ) (B : ℝ)
    (hf : StandingAssumptions f B) (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    ∫ S, (risk f D (A n S) - empRisk f S (A n S)) ∂(sampleLaw D n)
      = ∫ S, (f (A n (Fin.removeNth i S)) (S i)
          - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) ∂(sampleLaw D (n + 1)) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) i
  let G : Z × (Fin n → Z) → ℝ := fun p => f (A n p.2) p.1 - empRisk f p.2 (A n p.2)
  have hGm : Measurable G :=
    (meas_term f A hA n Prod.snd measurable_snd Prod.fst measurable_fst).sub
      (meas_empRisk f A hA n Prod.snd measurable_snd)
  have hGi : Integrable G (D.prod (Measure.pi fun _ : Fin n => D)) := by
    refine Integrable.of_bound hGm.aestronglyMeasurable (B + B)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hf.bounded _ _) (abs_empRisk_le f B hf.bounded hn _ _))
  unfold sampleLaw
  calc ∫ S, (risk f D (A n S) - empRisk f S (A n S)) ∂(Measure.pi fun _ : Fin n => D)
      = ∫ y, ∫ x, G (x, y) ∂D ∂(Measure.pi fun _ : Fin n => D) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun S => ?_)
        have hint : Integrable (fun x => f (A n S) x) D :=
          Integrable.of_bound (hf.measurable _).aestronglyMeasurable B
            (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs]; exact hf.bounded _ _)
        simp only [G]
        rw [integral_sub hint (integrable_const _), integral_const]
        simp [risk]
    _ = ∫ p, G p ∂(D.prod (Measure.pi fun _ : Fin n => D)) := (integral_prod_symm G hGi).symm
    _ = ∫ S, G (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) i S)
          ∂(Measure.pi fun _ : Fin (n + 1) => D) := (hmp.integral_comp' G).symm
    _ = _ := rfl

lemma empRisk_succ {H Z : Type*} (f : H → Z → ℝ) {n : ℕ} (hn : 1 ≤ n) (S : Fin (n + 1) → Z)
    (i : Fin (n + 1)) (h : H) :
    ((n : ℝ) + 1) * empRisk f S h = f h (S i) + (n : ℝ) * empRisk f (Fin.removeNth i S) h := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold empRisk
  rw [Fin.sum_univ_succAbove _ i]
  push_cast
  field_simp
  simp [Fin.removeNth]

lemma erm_le {H Z : Type*} (f : H → Z → ℝ) (B : ℝ) (hb : ∀ h z, |f h z| ≤ B) (A : Rule H Z)
    (hERM : IsERMRule f A) {k : ℕ} (hk : 1 ≤ k) (S : Fin k → Z) (h : H) :
    empRisk f S (A k S) ≤ empRisk f S h := by
  rw [hERM k hk S]
  refine ciInf_le ⟨-B, ?_⟩ h
  rintro _ ⟨h', rfl⟩
  exact (abs_le.mp (abs_empRisk_le f B hb (by omega) S h')).1

lemma pointwise {H Z : Type*} (f : H → Z → ℝ) (B : ℝ) (hb : ∀ h z, |f h z| ≤ B) (A : Rule H Z)
    (hERM : IsERMRule f A) {n : ℕ} (hn : 1 ≤ n) (S : Fin (n + 1) → Z) (i : Fin (n + 1)) :
    |empRisk f S (A (n + 1) S) - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))|
      ≤ 2 * B / ((n : ℝ) + 1) := by
  have hN : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := erm_le f B hb A hERM (k := n + 1) (by omega) S (A n (Fin.removeNth i S))
  have h2 := erm_le f B hb A hERM hn (Fin.removeNth i S) (A (n + 1) S)
  have e1 := empRisk_succ f hn S i (A (n + 1) S)
  have e2 := empRisk_succ f hn S i (A n (Fin.removeNth i S))
  have ba := abs_le.mp (hb (A (n + 1) S) (S i))
  have bb := abs_le.mp (hb (A n (Fin.removeNth i S)) (S i))
  have ta := abs_le.mp (abs_empRisk_le f B hb (by omega) (Fin.removeNth i S) (A (n + 1) S))
  have tb := abs_le.mp (abs_empRisk_le f B hb (by omega) (Fin.removeNth i S)
    (A n (Fin.removeNth i S)))
  have m1 := mul_le_mul_of_nonneg_left h1 hN.le
  have m2 := mul_le_mul_of_nonneg_left h2 hN.le
  rw [le_div_iff₀ hN, ← abs_of_pos hN, ← abs_mul, abs_le]
  constructor <;> nlinarith

end LearnStability.ERMLOO.P5e295723

open MeasureTheory LearnStability.ERMLOO in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (hERM : IsERMRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εstable : ℕ → ℝ)
    (hstable : LOOStable f A D εstable) :
    OnAverageGeneralizes f A D (fun n => εstable (n + 1) + 2 * B / (n + 1)) := by
  intro n hn
  have hpr := P5e295723.sampleLaw_prob D (n + 1)
  have hst := hstable n hn
  have hb := hf.bounded
  have hN : (0:ℝ) < (n : ℝ) + 1 := by positivity
  set μ := sampleLaw D (n + 1) with hμ
  set X := ∫ S, (risk f D (A n S) - empRisk f S (A n S)) ∂(sampleLaw D n) with hX
  show |X| ≤ εstable (n + 1) + 2 * B / ((n : ℝ) + 1)
  have ham : ∀ i : Fin (n + 1), Measurable (fun S : Fin (n + 1) → Z =>
      f (A n (Fin.removeNth i S)) (S i)) := fun i =>
    P5e295723.meas_term f A hA n (fun S : Fin (n + 1) → Z => Fin.removeNth i S) (P5e295723.measurable_removeNth i)
      (fun S : Fin (n + 1) → Z => S i)
      (measurable_pi_apply i)
  have hbm : ∀ i : Fin (n + 1), Measurable (fun S : Fin (n + 1) → Z => f (A (n + 1) S) (S i)) :=
    fun i => P5e295723.meas_term f A hA (n + 1) (fun S : Fin (n + 1) → Z => S) measurable_id
      (fun S : Fin (n + 1) → Z => S i) (measurable_pi_apply i)
  have hem : ∀ i : Fin (n + 1), Measurable (fun S : Fin (n + 1) → Z =>
      empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) := fun i =>
    P5e295723.meas_empRisk f A hA n (fun S : Fin (n + 1) → Z => Fin.removeNth i S)
      (P5e295723.measurable_removeNth i)
  have hae_int : ∀ i : Fin (n + 1), Integrable (fun S : Fin (n + 1) → Z =>
      f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) μ := fun i =>
    P5e295723.integrable_bdd D (n + 1) _ ((ham i).sub (hem i)) (B + B) fun S =>
      (abs_sub _ _).trans (add_le_add (hb _ _) (P5e295723.abs_empRisk_le f B hb (by omega) _ _))
  have hab_int : ∀ i : Fin (n + 1), Integrable (fun S : Fin (n + 1) → Z =>
      |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|) μ := fun i =>
    P5e295723.integrable_bdd D (n + 1) _ ((ham i).sub (hbm i)).abs (B + B) fun S => by
      rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hb _ _) (hb _ _))
  have hsum : ((n : ℝ) + 1) * X = ∫ S, ∑ i : Fin (n + 1), (f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hae_int i)]
    rw [Finset.sum_congr rfl (fun i _ => (P5e295723.transfer f B hf A hA D n hn i).symm)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  have hpt : ∀ S : Fin (n + 1) → Z, |∑ i : Fin (n + 1), (f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S)))|
      ≤ ∑ i : Fin (n + 1), |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
        + 2 * B := by
    intro S
    have hbs : ∑ i : Fin (n + 1), f (A (n + 1) S) (S i)
        = ((n : ℝ) + 1) * empRisk f S (A (n + 1) S) := by
      unfold empRisk; push_cast; field_simp
    have hsplit : ∑ i : Fin (n + 1), (f (A n (Fin.removeNth i S)) (S i)
        - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S)))
        = ∑ i : Fin (n + 1), (f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i))
          + ∑ i : Fin (n + 1), (empRisk f S (A (n + 1) S)
              - empRisk f (Fin.removeNth i S) (A n (Fin.removeNth i S))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hbs,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => P5e295723.pointwise f B hb A hERM hn S i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    rfl
  have hmain : ((n : ℝ) + 1) * |X| ≤ ∑ i : Fin (n + 1), ∫ S,
      |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)| ∂μ + 2 * B := by
    rw [← abs_of_pos hN, ← abs_mul, hsum]
    refine (abs_integral_le_integral_abs).trans ?_
    have hint2 : Integrable (fun S : Fin (n + 1) → Z => ∑ i : Fin (n + 1),
        |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)| + 2 * B) μ :=
      (integrable_finsetSum _ fun i _ => hab_int i).add (integrable_const _)
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun S => abs_nonneg _) hint2
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_add (integrable_finsetSum _ fun i _ => hab_int i) (integrable_const _),
      integral_finsetSum _ (fun i _ => hab_int i), integral_const]
    simp
  rw [div_le_iff₀ hN] at hst
  rw [← mul_le_mul_iff_of_pos_left hN, mul_add, mul_div_cancel₀ _ hN.ne']
  linarith
