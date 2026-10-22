-- Prove2me | solution 1 for LostSalesOldNew.LeadTime.optimality_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:44:19.180035+00:00
-- url     : https://prove2.me/submissions/89088326-a430-43b4-935a-0298db9e0d19

import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model



namespace LostSalesOldNew.LeadTime

open MeasureTheory
open LostSalesOldNew.StateReduction

lemma shift_cont {m : ℕ} : Continuous (fun p : (Fin (m + 1) → ℝ) × ℝ => shift p.1 p.2) := by
  refine continuous_pi fun i => ?_
  unfold shift
  split_ifs <;> fun_prop

lemma next_cont {L : ℕ} : Continuous (fun p : ((Fin L → ℝ) × ℝ) × ℝ => next p.1.1 p.1.2 p.2) := by
  have h1 : Continuous (fun p : (Fin L → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (L+1) → ℝ)) := by
    refine continuous_pi fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp; fun_prop
    · simp; fun_prop
  unfold next
  exact shift_cont.comp (h1.comp continuous_fst |>.prodMk continuous_snd)

lemma shift_nonneg {m : ℕ} (x : Fin (m + 1) → ℝ) (d : ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ shift x d i := by
  intro i
  unfold shift
  split_ifs
  · have := hx i.succ; have := hx 0; positivity
  · exact hx _

lemma next_nonneg {L : ℕ} (x : Fin L → ℝ) (z d : ℝ) (hx : ∀ i, 0 ≤ x i) (hz : 0 ≤ z) :
    ∀ i, 0 ≤ next x z d i := by
  apply shift_nonneg
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hz
  · simpa using hx j

lemma shift_norm_le {m : ℕ} (x : Fin (m + 1) → ℝ) (d : ℝ) : ‖shift x d‖ ≤ 2 * ‖x‖ + |d| := by
  have h0 : 0 ≤ 2 * ‖x‖ + |d| := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  unfold shift
  have h1 : |x i.succ| ≤ ‖x‖ := by simpa using norm_le_pi_norm x i.succ
  have h2 : |x 0| ≤ ‖x‖ := by simpa using norm_le_pi_norm x 0
  rw [Real.norm_eq_abs]
  split_ifs
  · have h3 : |max (x 0 - d) 0| ≤ |x 0| + |d| := by
      rcases le_total (x 0 - d) 0 with h | h
      · rw [max_eq_right h]; simp; positivity
      · rw [max_eq_left h]; exact abs_sub _ _
    have h4 := abs_add_le (max (x 0 - d) 0) (x i.succ)
    linarith
  · have := norm_nonneg x; linarith [abs_nonneg d]

lemma shift_sub_norm_le {m : ℕ} (x x' : Fin (m + 1) → ℝ) (d : ℝ) :
    ‖shift x d - shift x' d‖ ≤ 2 * ‖x - x'‖ := by
  have h0 : 0 ≤ 2 * ‖x - x'‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  have h1 : |x i.succ - x' i.succ| ≤ ‖x - x'‖ := by simpa using norm_le_pi_norm (x - x') i.succ
  have h2 : |x 0 - x' 0| ≤ ‖x - x'‖ := by simpa using norm_le_pi_norm (x - x') 0
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  unfold shift
  split_ifs
  · have : |max (x 0 - d) 0 - max (x' 0 - d) 0| ≤ |x 0 - x' 0| := by
      have := abs_max_sub_max_le_abs (x 0 - d) (x' 0 - d) 0
      simpa using this
    calc |max (x 0 - d) 0 + x i.succ - (max (x' 0 - d) 0 + x' i.succ)|
        = |(max (x 0 - d) 0 - max (x' 0 - d) 0) + (x i.succ - x' i.succ)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  · linarith [norm_nonneg (x - x')]


lemma yAfter_succ (l : ℕ) (x : Fin (l + 2) → ℝ) (ds : Fin (l + 1) → ℝ) :
    yAfter (l + 1) x ds = yAfter l (shift x (ds 0)) (Fin.tail ds) := rfl

lemma yAfter_bound : ∀ (l : ℕ) (x : Fin (l + 1) → ℝ) (ds : Fin l → ℝ),
    |yAfter l x ds| ≤ 2 ^ l * (‖x‖ + ∑ j, |ds j|)
  | 0, x, ds => by
    simp only [yAfter, pow_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero, one_mul]
    simpa using norm_le_pi_norm x 0
  | l + 1, x, ds => by
    rw [yAfter_succ]
    have ih := yAfter_bound l (shift x (ds 0)) (Fin.tail ds)
    have h1 := shift_norm_le x (ds 0)
    rw [Fin.sum_univ_succ]
    have h2 : (0:ℝ) ≤ ∑ j : Fin l, |ds j.succ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h3 : (0:ℝ) < 2 ^ l := by positivity
    calc _ ≤ 2 ^ l * (‖shift x (ds 0)‖ + ∑ j, |Fin.tail ds j|) := ih
      _ ≤ 2 ^ l * (2 * ‖x‖ + |ds 0| + ∑ j : Fin l, |ds j.succ|) := by
          apply mul_le_mul_of_nonneg_left _ h3.le
          simp only [Fin.tail]; linarith
      _ ≤ _ := by
          rw [pow_succ]
          have := norm_nonneg x
          have := abs_nonneg (ds 0)
          nlinarith

lemma yAfter_sub : ∀ (l : ℕ) (x x' : Fin (l + 1) → ℝ) (ds : Fin l → ℝ),
    |yAfter l x ds - yAfter l x' ds| ≤ 2 ^ l * ‖x - x'‖
  | 0, x, x', ds => by
    simp only [yAfter, pow_zero, one_mul]
    simpa using norm_le_pi_norm (x - x') 0
  | l + 1, x, x', ds => by
    rw [yAfter_succ, yAfter_succ]
    have ih := yAfter_sub l (shift x (ds 0)) (shift x' (ds 0)) (Fin.tail ds)
    have h1 := shift_sub_norm_le x x' (ds 0)
    have h3 : (0:ℝ) < 2 ^ l := by positivity
    calc _ ≤ _ := ih
      _ ≤ 2 ^ l * (2 * ‖x - x'‖) := mul_le_mul_of_nonneg_left h1 h3.le
      _ = _ := by rw [pow_succ]; ring

lemma yAfter_cont : ∀ (l : ℕ),
    Continuous (fun p : (Fin (l + 1) → ℝ) × (Fin l → ℝ) => yAfter l p.1 p.2)
  | 0 => by
    simp only [yAfter]; fun_prop
  | l + 1 => by
    have ih := yAfter_cont l
    have h1 : Continuous (fun p : (Fin (l + 2) → ℝ) × (Fin (l + 1) → ℝ) =>
        (shift p.1 (p.2 0), Fin.tail p.2)) := by
      refine Continuous.prodMk ?_ ?_
      · exact shift_cont.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
      · refine continuous_pi fun j => ?_
        simp only [Fin.tail]
        exact (continuous_apply _).comp continuous_snd
    exact ih.comp h1

lemma yAfter_ge_last : ∀ (l : ℕ), 1 ≤ l → ∀ (x : Fin (l + 1) → ℝ) (ds : Fin l → ℝ),
    x (Fin.last l) ≤ yAfter l x ds := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    intro x ds
    show x 1 ≤ shift x (ds 0) 0
    simp only [shift, Fin.val_zero, if_true]
    have := le_max_right (x 0 - ds 0) 0
    show x (Fin.last 1) ≤ max (x 0 - ds 0) 0 + x (Fin.succ 0)
    have : Fin.last 1 = Fin.succ 0 := rfl
    rw [this]; linarith [le_max_right (x 0 - ds 0) 0]
  | succ l hl ih =>
    intro x ds
    rw [yAfter_succ]
    refine le_trans ?_ (ih (shift x (ds 0)) (Fin.tail ds))
    simp only [shift]
    have : ¬ ((Fin.last l : Fin (l + 1)) : ℕ) = 0 := by simp; omega
    rw [if_neg this]
    rfl

lemma yAfter_nonneg : ∀ (l : ℕ) (x : Fin (l + 1) → ℝ) (ds : Fin l → ℝ), (∀ i, 0 ≤ x i) →
    0 ≤ yAfter l x ds
  | 0, x, ds, hx => hx 0
  | l + 1, x, ds, hx => by
    rw [yAfter_succ]
    exact yAfter_nonneg l _ _ (shift_nonneg x _ hx)


section Q0

variable (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]

lemma int_max1 (hmean : Integrable (fun d : ℝ => d) D) (y : ℝ) :
    Integrable (fun d : ℝ => max (y - d) 0) D := by
  refine Integrable.mono' ((integrable_const |y|).add hmean.abs) (by fun_prop) (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  show _ ≤ |y| + |d|
  refine max_le ?_ (by positivity)
  have := le_abs_self y; have := neg_abs_le d; linarith

lemma int_max2 (hmean : Integrable (fun d : ℝ => d) D) (y : ℝ) :
    Integrable (fun d : ℝ => max (d - y) 0) D := by
  refine Integrable.mono' ((integrable_const |y|).add hmean.abs) (by fun_prop) (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  show _ ≤ |y| + |d|
  refine max_le ?_ (by positivity)
  have := neg_abs_le y; have := le_abs_self d; linarith

lemma q0_lip (hmean : Integrable (fun d : ℝ => d) D) (y y' : ℝ) :
    |q0 K D y - q0 K D y'| ≤ (K.c + |K.h| + K.p) * |y - y'| := by
  have e1 : |∫ d, max (y - d) 0 ∂D - ∫ d, max (y' - d) 0 ∂D| ≤ |y - y'| := by
    rw [← integral_sub (int_max1 D hmean y) (int_max1 D hmean y')]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ d, |max (y - d) 0 - max (y' - d) 0| ∂D ≤ ∫ d, |y - y'| ∂D := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _) (Filter.Eventually.of_forall fun d => ?_)
          have := abs_max_sub_max_le_abs (y - d) (y' - d) 0
          simpa using this
      _ = |y - y'| := by simp
  have e2 : |∫ d, max (d - y) 0 ∂D - ∫ d, max (d - y') 0 ∂D| ≤ |y - y'| := by
    rw [← integral_sub (int_max2 D hmean y) (int_max2 D hmean y')]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ d, |max (d - y) 0 - max (d - y') 0| ∂D ≤ ∫ d, |y - y'| ∂D := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _) (Filter.Eventually.of_forall fun d => ?_)
          have := abs_max_sub_max_le_abs (d - y) (d - y') 0
          have h : |d - y - (d - y')| = |y - y'| := by rw [← abs_neg]; ring_nf
          simpa [h, abs_sub_comm y' y] using this
      _ = |y - y'| := by simp
  unfold q0
  have hc := K.c_nonneg
  have hp := K.p_nonneg
  set A := ∫ d, max (y - d) 0 ∂D
  set A' := ∫ d, max (y' - d) 0 ∂D
  set B := ∫ d, max (d - y) 0 ∂D
  set B' := ∫ d, max (d - y') 0 ∂D
  have : K.c * y + K.h * A + K.p * B - (K.c * y' + K.h * A' + K.p * B') =
      K.c * (y - y') + K.h * (A - A') + K.p * (B - B') := by ring
  rw [this]
  calc _ ≤ |K.c * (y - y')| + |K.h * (A - A')| + |K.p * (B - B')| := abs_add_three _ _ _
    _ = K.c * |y - y'| + |K.h| * |A - A'| + K.p * |B - B'| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hp]
    _ ≤ K.c * |y - y'| + |K.h| * |y - y'| + K.p * |y - y'| := by
        gcongr
    _ = _ := by ring

lemma q0_cont (hmean : Integrable (fun d : ℝ => d) D) : Continuous (q0 K D) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  refine Metric.continuousAt_iff.2 fun ε hε => ?_
  have hM : 0 < K.c + |K.h| + K.p + 1 := by
    have := K.c_nonneg; have := K.p_nonneg; positivity
  refine ⟨ε / (K.c + |K.h| + K.p + 1), by positivity, fun y' hy' => ?_⟩
  rw [Real.dist_eq] at hy' ⊢
  have h := q0_lip K D hmean y' y
  have hM0 : 0 ≤ K.c + |K.h| + K.p := by have := K.c_nonneg; have := K.p_nonneg; positivity
  calc |q0 K D y' - q0 K D y| ≤ _ := h
    _ ≤ (K.c + |K.h| + K.p + 1) * |y' - y| := by nlinarith [abs_nonneg (y' - y)]
    _ < (K.c + |K.h| + K.p + 1) * (ε / (K.c + |K.h| + K.p + 1)) := by
        apply mul_lt_mul_of_pos_left hy' hM
    _ = ε := by field_simp

lemma q0_abs_le (hmean : Integrable (fun d : ℝ => d) D) (y : ℝ) :
    |q0 K D y| ≤ |q0 K D 0| + (K.c + |K.h| + K.p) * |y| := by
  have := q0_lip K D hmean y 0
  simp only [sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (q0 K D y) (q0 K D 0)
  linarith

omit [IsProbabilityMeasure D] in
lemma ae_nonneg_D (hD : LostSalesOldNew.StateReduction.IsDemand D) : ∀ᵐ d ∂D, 0 ≤ d := by
  have := hD.nonneg
  rw [ae_iff]
  simpa [Set.Iio] using this

lemma q0_lower (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (y : ℝ) (hy : 0 ≤ y) :
    (K.c + K.h) * y - |K.h| * ∫ d, d ∂D ≤ q0 K D y := by
  have hnn : 0 ≤ ∫ d, d ∂D := integral_nonneg_of_ae (ae_nonneg_D D hD)
  have i1 : ∫ d, max (y - d) 0 ∂D ≤ y := by
    have := integral_mono_ae (int_max1 D hmean y) (integrable_const y) (by
      filter_upwards [ae_nonneg_D D hD] with d hd
      exact max_le (by linarith) hy)
    simpa using this
  have i2 : y - ∫ d, d ∂D ≤ ∫ d, max (y - d) 0 ∂D := by
    have h1 : Integrable (fun d : ℝ => y - d) D := (integrable_const y).sub hmean
    have := integral_mono h1 (int_max1 D hmean y) (fun d => le_max_left (y - d) 0)
    rw [integral_sub (integrable_const y) hmean] at this
    simpa using this
  have i3 : 0 ≤ ∫ d, max (d - y) 0 ∂D := integral_nonneg fun d => le_max_right _ _
  unfold q0
  have hp := K.p_nonneg
  have : 0 ≤ K.p * ∫ d, max (d - y) 0 ∂D := mul_nonneg hp i3
  rcases le_total 0 K.h with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_nonpos h]
    nlinarith

end Q0


lemma snoc_cont {L : ℕ} : Continuous (fun p : (Fin L → ℝ) × ℝ =>
    (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (L+1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp; fun_prop
  · simp; fun_prop

section QL

variable (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]

lemma kappa_nonneg : 0 ≤ K.c + K.h := by
  unfold Costs.h
  have := K.hhat_nonneg; have := K.c_nonneg; have := K.γ_lt_one
  nlinarith

lemma q0_nonneg (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (y : ℝ) (hy : 0 ≤ y) : 0 ≤ q0 K D y := by
  have i1 : ∫ d, max (y - d) 0 ∂D ≤ y := by
    have := integral_mono_ae (int_max1 D hmean y) (integrable_const y) (by
      filter_upwards [ae_nonneg_D D hD] with d hd
      exact max_le (by linarith) hy)
    simpa using this
  have i0 : 0 ≤ ∫ d, max (y - d) 0 ∂D := integral_nonneg fun d => le_max_right _ _
  have i3 : 0 ≤ ∫ d, max (d - y) 0 ∂D := integral_nonneg fun d => le_max_right _ _
  unfold q0
  have hp := K.p_nonneg
  have hc := K.c_nonneg
  have hk := kappa_nonneg K
  have : 0 ≤ K.p * ∫ d, max (d - y) 0 ∂D := mul_nonneg hp i3
  rcases le_total 0 K.h with h | h
  · have := mul_nonneg h i0
    have := mul_nonneg hc hy
    linarith
  · nlinarith

lemma int_q0y (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l + 1) → ℝ) :
    Integrable (fun ds : Fin l → ℝ => q0 K D (yAfter l x ds)) (Measure.pi fun _ : Fin l => D) := by
  have hc : Continuous (fun ds : Fin l → ℝ => q0 K D (yAfter l x ds)) :=
    (q0_cont K D hmean).comp ((yAfter_cont l).comp (continuous_const.prodMk continuous_id))
  have hint : Integrable (fun ds : Fin l → ℝ => |q0 K D 0| + (K.c + |K.h| + K.p) * (2 ^ l * (‖x‖ + ∑ j, |ds j|)))
      (Measure.pi fun _ : Fin l => D) := by
    refine (integrable_const _).add (Integrable.const_mul ?_ _)
    refine Integrable.const_mul ((integrable_const _).add ?_) _
    refine integrable_finsetSum _ fun j _ => ?_
    exact (integrable_eval (μ := fun _ : Fin l => D) (i := j) hmean).abs
  refine Integrable.mono' hint hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ds => ?_)
  rw [Real.norm_eq_abs]
  refine (q0_abs_le K D hmean _).trans ?_
  have := yAfter_bound l x ds
  have hM : 0 ≤ K.c + |K.h| + K.p := by have := K.c_nonneg; have := K.p_nonneg; positivity
  have := mul_le_mul_of_nonneg_left this hM
  linarith [abs_nonneg (yAfter l x ds)]

lemma qL_lip (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x x' : Fin (l + 1) → ℝ) :
    |qL K D l x - qL K D l x'| ≤ K.γ ^ l * ((K.c + |K.h| + K.p) * 2 ^ l) * ‖x - x'‖ := by
  unfold qL
  rw [← mul_sub, ← integral_sub (int_q0y K D hmean l x) (int_q0y K D hmean l x'), abs_mul,
    abs_of_nonneg (pow_nonneg K.γ_nonneg l)]
  have hM : 0 ≤ K.c + |K.h| + K.p := by have := K.c_nonneg; have := K.p_nonneg; positivity
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg K.γ_nonneg l)
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ds, |q0 K D (yAfter l x ds) - q0 K D (yAfter l x' ds)| ∂(Measure.pi fun _ : Fin l => D)
      ≤ ∫ ds : Fin l → ℝ, (K.c + |K.h| + K.p) * 2 ^ l * ‖x - x'‖ ∂(Measure.pi fun _ : Fin l => D) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun ds => ?_)
        refine (q0_lip K D hmean _ _).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (yAfter_sub l x x' ds) hM
    _ = _ := by simp

lemma qL_cont (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) : Continuous (qL K D l) := by
  have : LipschitzWith (Real.toNNReal (K.γ ^ l * ((K.c + |K.h| + K.p) * 2 ^ l))) (qL K D l) := by
    refine LipschitzWith.of_dist_le' fun x x' => ?_
    rw [Real.dist_eq, dist_eq_norm]
    exact qL_lip K D hmean l x x'
  exact this.continuous

lemma qL_snoc_cont (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) :
    Continuous (fun p : (Fin L → ℝ) × ℝ => qL K D L (Fin.snoc (α := fun _ => ℝ) p.1 p.2)) :=
  (qL_cont K D hmean L).comp snoc_cont

lemma qL_nonneg (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ qL K D l x := by
  unfold qL
  refine mul_nonneg (pow_nonneg K.γ_nonneg l) (integral_nonneg fun ds => ?_)
  exact q0_nonneg K D hD hmean _ (yAfter_nonneg l x ds hx)

lemma qL_lower (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L) (x : Fin L → ℝ) (z : ℝ) (hz : 0 ≤ z) :
    K.γ ^ L * ((K.c + K.h) * z - |K.h| * ∫ d, d ∂D) ≤ qL K D L (Fin.snoc (α := fun _ => ℝ) x z) := by
  unfold qL
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg K.γ_nonneg L)
  have := integral_mono (integrable_const ((K.c + K.h) * z - |K.h| * ∫ d, d ∂D))
    (int_q0y K D hmean L (Fin.snoc (α := fun _ => ℝ) x z)) (fun ds => by
      have hy := yAfter_ge_last L hL (Fin.snoc (α := fun _ => ℝ) x z) ds
      simp only [Fin.snoc_last] at hy
      have h1 := q0_lower K D hD hmean _ (hz.trans hy)
      have := kappa_nonneg K
      nlinarith)
  simpa using this


lemma qL_succ_aux (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l + 2) → ℝ) :
    Integrable (fun p : ℝ × (Fin l → ℝ) => q0 K D (yAfter l (shift x p.1) p.2))
      (D.prod (Measure.pi fun _ : Fin l => D)) ∧
    ∫ ds, q0 K D (yAfter (l + 1) x ds) ∂(Measure.pi fun _ : Fin (l + 1) => D) =
      ∫ d, ∫ ds, q0 K D (yAfter l (shift x d) ds) ∂(Measure.pi fun _ : Fin l => D) ∂D := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (l + 1) => ℝ) 0 with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (l + 1) => D) 0
  set g : ℝ × (Fin l → ℝ) → ℝ := fun p => q0 K D (yAfter l (shift x p.1) p.2) with hg
  have hcomp : ∀ ds : Fin (l + 1) → ℝ, q0 K D (yAfter (l + 1) x ds) = g (e ds) := by
    intro ds
    rw [yAfter_succ]
    simp [hg, he, MeasurableEquiv.piFinSuccAbove_apply, Fin.succAbove_zero, Fin.tail]
  have hint0 := int_q0y K D hmean (l + 1) x
  have hint : Integrable g (D.prod (Measure.pi fun _ : Fin l => D)) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    refine hint0.congr (Filter.Eventually.of_forall fun ds => ?_)
    exact hcomp ds
  refine ⟨hint, ?_⟩
  calc _ = ∫ ds, g (e ds) ∂(Measure.pi fun _ : Fin (l + 1) => D) := by
        refine integral_congr_ae (Filter.Eventually.of_forall hcomp)
    _ = ∫ p, g p ∂(D.prod (Measure.pi fun _ : Fin l => D)) := hmp.integral_comp' g
    _ = _ := integral_prod g hint

lemma qL_succ (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l + 2) → ℝ) :
    qL K D (l + 1) x = K.γ * ∫ d, qL K D l (shift x d) ∂D := by
  obtain ⟨hint, heq⟩ := qL_succ_aux K D hmean l x
  unfold qL
  rw [heq]
  simp only [integral_const_mul]
  ring

lemma qL_succ_int (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l + 2) → ℝ) :
    Integrable (fun d => qL K D l (shift x d)) D := by
  obtain ⟨hint, heq⟩ := qL_succ_aux K D hmean l x
  exact (hint.integral_prod_left).const_mul (K.γ ^ l)

lemma qL_succ_ofReal (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l + 2) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ENNReal.ofReal (qL K D (l + 1) x) =
      ENNReal.ofReal K.γ * ∫⁻ d, ENNReal.ofReal (qL K D l (shift x d)) ∂D := by
  rw [qL_succ K D hmean, ENNReal.ofReal_mul K.γ_nonneg,
    ofReal_integral_eq_lintegral_ofReal (qL_succ_int K D hmean l x)
      (Filter.Eventually.of_forall fun d => qL_nonneg K D hD hmean l _ (shift_nonneg x d hx))]

end QL


section Generic

lemma lsc_comp_cont {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ENNReal}
    (hf : LowerSemicontinuous f) {φ : X → Y} (hφ : Continuous φ) : LowerSemicontinuous (f ∘ φ) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hf ⊢
  intro y
  exact (hf y).preimage hφ

lemma inf_lsc {X : Type*} [TopologicalSpace X] (g : X × ℝ → ENNReal) (hg : LowerSemicontinuous g)
    (κ' C' : ℝ) (hκ : 0 < κ') (hc : ∀ x z, 0 ≤ z → ENNReal.ofReal (κ' * z - C') ≤ g (x, z)) :
    LowerSemicontinuous (fun x => ⨅ z, ⨅ (_ : 0 ≤ z), g (x, z)) := by
  intro x0 y hy
  obtain ⟨y', hyy', hy'f⟩ := exists_between hy
  have hy'top : y' ≠ ⊤ := ne_top_of_lt hy'f
  set M : ℝ := (C' + y'.toReal + 1) / κ' with hM
  have hA : ∀ x z, 0 ≤ z → M < z → y' < g (x, z) := by
    intro x z hz0 hz
    refine lt_of_lt_of_le ?_ (hc x z hz0)
    rw [ENNReal.lt_ofReal_iff_toReal_lt hy'top]
    have : C' + y'.toReal + 1 < κ' * z := by
      have := (div_lt_iff₀ hκ).1 hz
      linarith
    linarith
  have hn : IsOpen (g ⁻¹' Set.Ioi y') := hg.isOpen_preimage y'
  have hsub : ({x0} : Set X) ×ˢ Set.Icc 0 M ⊆ g ⁻¹' Set.Ioi y' := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have : a = x0 := ha
    subst this
    simpa using lt_of_lt_of_le hy'f (iInf₂_le (f := fun z (_ : 0 ≤ z) => g (a, z)) b hb.1)
  obtain ⟨u, v, hu, hv, hxu, hMv, huv⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hn hsub
  filter_upwards [hu.mem_nhds (hxu rfl)] with x' hx'
  refine lt_of_lt_of_le hyy' (le_iInf₂ fun z hz => ?_)
  by_cases hzM : z ≤ M
  · exact le_of_lt (huv ⟨hx', hMv ⟨hz, hzM⟩⟩)
  · exact le_of_lt (hA x' z hz (not_le.1 hzM))


lemma attain_min (g : ℝ → ENNReal) (hg : LowerSemicontinuous g) (κ' C' : ℝ) (hκ : 0 < κ')
    (hc : ∀ z, 0 ≤ z → ENNReal.ofReal (κ' * z - C') ≤ g z) :
    ∃ z0, 0 ≤ z0 ∧ ∀ z, 0 ≤ z → g z0 ≤ g z := by
  set m : ENNReal := ⨅ z, ⨅ (_ : 0 ≤ z), g z with hm
  by_cases hmt : m = ⊤
  · refine ⟨0, le_rfl, fun z hz => ?_⟩
    have : m ≤ g z := iInf₂_le z hz
    rw [hmt] at this
    exact le_trans le_top this
  · have hm1 : m + 1 ≠ ⊤ := by simpa using hmt
    set M : ℝ := (C' + (m + 1).toReal + 1) / κ' with hM
    have hA : ∀ z, 0 ≤ z → M < z → m + 1 < g z := by
      intro z hz0 hz
      refine lt_of_lt_of_le ?_ (hc z hz0)
      rw [ENNReal.lt_ofReal_iff_toReal_lt hm1]
      have : C' + (m + 1).toReal + 1 < κ' * z := by
        have := (div_lt_iff₀ hκ).1 hz
        linarith
      linarith
    have hex : ∃ z'', 0 ≤ z'' ∧ g z'' < m + 1 := by
      have : m < m + 1 := ENNReal.lt_add_right hmt one_ne_zero
      rw [hm, iInf_lt_iff] at this
      obtain ⟨z, hz⟩ := this
      rw [iInf_lt_iff] at hz
      obtain ⟨h0, hz⟩ := hz
      exact ⟨z, h0, hz⟩
    obtain ⟨z'', hz''0, hz''⟩ := hex
    have hz''M : z'' ≤ M := by
      by_contra h
      exact absurd (hA z'' hz''0 (not_le.1 h)) (not_lt.2 hz''.le)
    have hM0 : 0 ≤ M := hz''0.trans hz''M
    obtain ⟨z0, hz0, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (Set.nonempty_Icc.2 hM0)
      isCompact_Icc (hg.lowerSemicontinuousOn (Set.Icc 0 M))
    refine ⟨z0, hz0.1, fun z hz => ?_⟩
    by_cases hzM : z ≤ M
    · exact hmin ⟨hz, hzM⟩
    · have h1 : g z0 ≤ g z'' := hmin ⟨hz''0, hz''M⟩
      exact (h1.trans hz''.le).trans (hA z hz (not_le.1 hzM)).le

lemma common_min (g : ℕ → ℝ → ENNReal) (hlsc : ∀ n, LowerSemicontinuous (g n))
    (hmono : ∀ n z, g n z ≤ g (n + 1) z) (κ' C' : ℝ) (hκ : 0 < κ')
    (hc : ∀ n z, 0 ≤ z → ENNReal.ofReal (κ' * z - C') ≤ g n z) :
    ∃ z, 0 ≤ z ∧ ∀ n, g n z ≤ ⨆ n, ⨅ w, ⨅ (_ : 0 ≤ w), g n w := by
  set a := ⨆ n, ⨅ w, ⨅ (_ : 0 ≤ w), g n w with ha
  by_cases hat : a = ⊤
  · exact ⟨0, le_rfl, fun n => by rw [hat]; exact le_top⟩
  · have hmono' : ∀ n m, n ≤ m → ∀ z, g n z ≤ g m z := by
      intro n m hnm z
      induction hnm with
      | refl => exact le_rfl
      | step _ ih => exact ih.trans (hmono _ _)
    set M : ℝ := (C' + a.toReal) / κ' with hM
    have hbd : ∀ n z, 0 ≤ z → g n z ≤ a → z ≤ M := by
      intro n z hz hga
      have h1 := (hc n z hz).trans hga
      rw [ENNReal.ofReal_le_iff_le_toReal hat] at h1
      rw [hM, le_div_iff₀ hκ]
      linarith
    set S : ℕ → Set ℝ := fun n => {z | 0 ≤ z ∧ g n z ≤ a} with hS
    have hSsub : ∀ n, S n ⊆ Set.Icc 0 M := fun n z hz => ⟨hz.1, hbd n z hz.1 hz.2⟩
    have hScl : ∀ n, IsClosed (S n) := by
      intro n
      have : S n = Set.Ici 0 ∩ {z | g n z ≤ a} := by
        ext z; simp [hS]
      rw [this]
      exact isClosed_Ici.inter ((hlsc n).isClosed_preimage a)
    have hSne : ∀ n, (S n).Nonempty := by
      intro n
      obtain ⟨z0, hz0, hmin⟩ := attain_min (g n) (hlsc n) κ' C' hκ (hc n)
      refine ⟨z0, hz0, ?_⟩
      have : g n z0 ≤ ⨅ w, ⨅ (_ : 0 ≤ w), g n w := le_iInf₂ fun w hw => hmin w hw
      exact this.trans (le_iSup (fun n => ⨅ w, ⨅ (_ : 0 ≤ w), g n w) n)
    have hSd : ∀ n, S (n + 1) ⊆ S n := by
      intro n z hz
      exact ⟨hz.1, (hmono n z).trans hz.2⟩
    obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSne
      (isCompact_Icc.of_isClosed_subset (hScl 0) (hSsub 0)) hScl
    rw [Set.mem_iInter] at hz
    exact ⟨z, (hz 0).1, fun n => (hz n).2⟩

end Generic


section DP

variable (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]

noncomputable def GG (L : ℕ) (f : (Fin L → ℝ) → ENNReal) (x : Fin L → ℝ) (z : ℝ) : ENNReal :=
  ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
    + ENNReal.ofReal K.γ * ∫⁻ d, f (next x z d) ∂D

lemma bellman_def (L : ℕ) (f : (Fin L → ℝ) → ENNReal) (x : Fin L → ℝ) :
    bellman K D L f x = ⨅ z, ⨅ (_ : 0 ≤ z), GG K D L f x z := rfl

lemma GG_mono (L : ℕ) {f f' : (Fin L → ℝ) → ENNReal} (h : ∀ x, f x ≤ f' x) (x : Fin L → ℝ) (z : ℝ) :
    GG K D L f x z ≤ GG K D L f' x z := by
  unfold GG
  gcongr
  exact h _

lemma bellman_mono (L : ℕ) {f f' : (Fin L → ℝ) → ENNReal} (h : ∀ x, f x ≤ f' x) (x : Fin L → ℝ) :
    bellman K D L f x ≤ bellman K D L f' x := by
  rw [bellman_def, bellman_def]
  exact iInf_mono fun z => iInf_mono fun hz => GG_mono K D L h x z

lemma fH_mono (L : ℕ) : ∀ n x, fH K D L n x ≤ fH K D L (n + 1) x := by
  intro n
  induction n with
  | zero => intro x; simp [fH]
  | succ n ih =>
    intro x
    show bellman K D L (fH K D L n) x ≤ bellman K D L (fH K D L (n + 1)) x
    exact bellman_mono K D L ih x

lemma fH_mono' (L : ℕ) {n m : ℕ} (h : n ≤ m) (x : Fin L → ℝ) : fH K D L n x ≤ fH K D L m x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (fH_mono K D L _ x)

lemma fStar_eq_succ (L : ℕ) (x : Fin L → ℝ) : fStar K D L x = ⨆ n, fH K D L (n + 1) x := by
  unfold fStar
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact (fH_mono K D L n x).trans (le_iSup (fun n => fH K D L (n + 1) x) n)
  · exact iSup_le fun n => le_iSup (fun n => fH K D L n x) (n + 1)

lemma GG_lsc (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) {f : (Fin L → ℝ) → ENNReal}
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun p : (Fin L → ℝ) × ℝ => GG K D L f p.1 p.2) := by
  have h1 : LowerSemicontinuous (fun p : (Fin L → ℝ) × ℝ =>
      ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) p.1 p.2))) :=
    (ENNReal.continuous_ofReal.comp (qL_snoc_cont K D hmean L)).lowerSemicontinuous
  have hnd : ∀ d : ℝ, Continuous (fun p : (Fin L → ℝ) × ℝ => next p.1 p.2 d) := fun d =>
    next_cont.comp (continuous_id.prodMk continuous_const)
  have hnp : ∀ p : (Fin L → ℝ) × ℝ, Continuous (fun d : ℝ => next p.1 p.2 d) := fun p =>
    next_cont.comp (continuous_const.prodMk continuous_id)
  have h2 : LowerSemicontinuous (fun p : (Fin L → ℝ) × ℝ => ∫⁻ d, f (next p.1 p.2 d) ∂D) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro p
    calc ∫⁻ d, f (next p.1 p.2 d) ∂D
        ≤ ∫⁻ d, Filter.liminf (fun p' : (Fin L → ℝ) × ℝ => f (next p'.1 p'.2 d)) (nhds p) ∂D :=
          lintegral_mono fun d => (lsc_comp_cont hf (hnd d)).le_liminf p
      _ ≤ Filter.liminf (fun p' : (Fin L → ℝ) × ℝ => ∫⁻ d, f (next p'.1 p'.2 d) ∂D) (nhds p) :=
          lintegral_liminf_le fun p' => hf.measurable.comp (hnp p').measurable
  have h3 : LowerSemicontinuous (fun p : (Fin L → ℝ) × ℝ =>
      ENNReal.ofReal K.γ * ∫⁻ d, f (next p.1 p.2 d) ∂D) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous h2
      (fun a b hab => mul_le_mul_right hab _)
  exact h1.add h3


lemma GG_coercive (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L) (f : (Fin L → ℝ) → ENNReal)
    (x : Fin L → ℝ) (z : ℝ) (hz : 0 ≤ z) :
    ENNReal.ofReal (K.γ ^ L * (K.c + K.h) * z - K.γ ^ L * (|K.h| * ∫ d, d ∂D)) ≤ GG K D L f x z := by
  unfold GG
  refine le_trans ?_ le_self_add
  refine ENNReal.ofReal_le_ofReal ?_
  have := qL_lower K D hD hmean L hL x z hz
  linarith

lemma fH_lsc (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L) (hγ : 0 < K.γ)
    (hκ : 0 < K.c + K.h) : ∀ n, LowerSemicontinuous (fH K D L n) := by
  intro n
  induction n with
  | zero => exact (continuous_const (y := (0 : ENNReal))).lowerSemicontinuous
  | succ n ih =>
    have hk : 0 < K.γ ^ L * (K.c + K.h) := by positivity
    have := inf_lsc (fun p : (Fin L → ℝ) × ℝ => GG K D L (fH K D L n) p.1 p.2)
      (GG_lsc K D hmean L ih) (K.γ ^ L * (K.c + K.h)) (K.γ ^ L * (|K.h| * ∫ d, d ∂D)) hk
      (fun x z hz => GG_coercive K D hD hmean L hL _ x z hz)
    exact this

lemma fStar_lsc (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L) (hγ : 0 < K.γ)
    (hκ : 0 < K.c + K.h) : LowerSemicontinuous (fStar K D L) :=
  lowerSemicontinuous_iSup (fun n => fH_lsc K D hD hmean L hL hγ hκ n)

lemma GG_fStar (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L) (hγ : 0 < K.γ)
    (hκ : 0 < K.c + K.h) (x : Fin L → ℝ) (z : ℝ) :
    GG K D L (fStar K D L) x z = ⨆ n, GG K D L (fH K D L n) x z := by
  unfold GG
  have hmeas : ∀ n, Measurable (fun d => fH K D L n (next x z d)) := fun n =>
    (fH_lsc K D hD hmean L hL hγ hκ n).measurable.comp
      (show Continuous (fun d : ℝ => next x z d) from
        next_cont.comp ((continuous_const (y := (x, z))).prodMk continuous_id)).measurable
  have hmono : Monotone (fun n => fun d => fH K D L n (next x z d)) :=
    monotone_nat_of_le_succ fun n d => fH_mono K D L n _
  have : ∫⁻ d, fStar K D L (next x z d) ∂D = ⨆ n, ∫⁻ d, fH K D L n (next x z d) ∂D := by
    rw [← lintegral_iSup hmeas hmono]
    rfl
  rw [this, ENNReal.mul_iSup, ENNReal.add_iSup]

theorem main_A (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L) (hγ : 0 < K.γ)
    (hκ : 0 < K.c + K.h) (x : Fin L → ℝ) :
    fStar K D L x = bellman K D L (fStar K D L) x ∧
      ∃ z : ℝ, 0 ≤ z ∧ fStar K D L x = GG K D L (fStar K D L) x z := by
  have hk : 0 < K.γ ^ L * (K.c + K.h) := by positivity
  set C' := K.γ ^ L * (|K.h| * ∫ d, d ∂D)
  have hlsc : ∀ n, LowerSemicontinuous (fun z => GG K D L (fH K D L n) x z) := fun n =>
    lsc_comp_cont (GG_lsc K D hmean L (fH_lsc K D hD hmean L hL hγ hκ n))
      (φ := fun z : ℝ => (x, z)) (by fun_prop)
  obtain ⟨z0, hz0, hz0le⟩ := common_min (fun n z => GG K D L (fH K D L n) x z) hlsc
    (fun n z => GG_mono K D L (fH_mono K D L n) x z) (K.γ ^ L * (K.c + K.h)) C' hk
    (fun n z hz => GG_coercive K D hD hmean L hL _ x z hz)
  have ha : (⨆ n, ⨅ w, ⨅ (_ : 0 ≤ w), GG K D L (fH K D L n) x w) = fStar K D L x := by
    rw [fStar_eq_succ]
    rfl
  rw [ha] at hz0le
  have h1 : fStar K D L x ≤ bellman K D L (fStar K D L) x := by
    rw [fStar_eq_succ]
    refine iSup_le fun n => ?_
    exact bellman_mono K D L (fun y => le_iSup (fun n => fH K D L n y) n) x
  have h2 : bellman K D L (fStar K D L) x ≤ GG K D L (fStar K D L) x z0 := by
    rw [bellman_def]; exact iInf₂_le z0 hz0
  have h3 : GG K D L (fStar K D L) x z0 ≤ fStar K D L x := by
    rw [GG_fStar K D hD hmean L hL hγ hκ]
    exact iSup_le hz0le
  exact ⟨le_antisymm h1 (h2.trans h3), z0, hz0, le_antisymm (h1.trans h2) h3⟩


lemma GG_mono_nonneg (L : ℕ) {f f' : (Fin L → ℝ) → ENNReal}
    (h : ∀ x, (∀ i, 0 ≤ x i) → f x ≤ f' x) (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) (z : ℝ) (hz : 0 ≤ z) :
    GG K D L f x z ≤ GG K D L f' x z := by
  unfold GG
  gcongr
  exact h _ (next_nonneg x z _ hx hz)

lemma fStar_le_of_fix (L : ℕ) (g : (Fin L → ℝ) → ENNReal)
    (hg : ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → g x = bellman K D L g x) :
    ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x ≤ g x := by
  have key : ∀ n, ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fH K D L n x ≤ g x := by
    intro n
    induction n with
    | zero => intro x _; simp [fH]
    | succ n ih =>
      intro x hx
      rw [hg x hx]
      show bellman K D L (fH K D L n) x ≤ bellman K D L g x
      rw [bellman_def, bellman_def]
      exact iInf_mono fun z => iInf_mono fun hz => GG_mono_nonneg K D L ih x hx z hz
  intro x hx
  exact iSup_le fun n => key n x hx

lemma ennreal_eq_zero_of_forall (a : ENNReal) (h : ∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal ε) : a = 0 := by
  have hne : a ≠ ⊤ := by
    intro ht
    have := h 1 one_pos
    rw [ht] at this
    exact absurd this (by simp)
  have h2 : a.toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h ε hε
    rw [← ENNReal.ofReal_toReal hne, ENNReal.ofReal_le_ofReal_iff hε.le] at this
    linarith
  have h3 : a.toReal = 0 := le_antisymm h2 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff a).1 h3 with h | h
  · exact h
  · exact absurd h hne

lemma J_tendsto (hmean : Integrable (fun d : ℝ => d) D) :
    Filter.Tendsto (fun z : ℝ => ∫ d, max (d - z) 0 ∂D) Filter.atTop (nhds 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := D) (l := Filter.atTop)
    (F := fun (z : ℝ) (d : ℝ) => max (d - z) 0) (f := fun _ => (0 : ℝ)) (bound := fun d => |d|)
    (Filter.Eventually.of_forall fun z => by fun_prop)
    ((Filter.eventually_ge_atTop (0 : ℝ)).mono fun z hz => Filter.Eventually.of_forall fun d => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self d]) (abs_nonneg d))
    hmean.abs
    (Filter.Eventually.of_forall fun d => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop d] with z hz
      simp [hz])
  simpa using this


lemma small_q (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L)
    (hB : (K.c = 0 ∧ K.hhat = 0) ∨ K.γ = 0) (x : Fin L → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℝ, 0 ≤ z ∧ qL K D L (Fin.snoc (α := fun _ => ℝ) x z) ≤ ε := by
  rcases hB with ⟨hc, hh⟩ | hγ
  · have hh0 : K.h = 0 := by simp [Costs.h, hc, hh]
    have hT := (J_tendsto D hmean).const_mul K.p
    rw [mul_zero] at hT
    obtain ⟨z, hz, hz0⟩ := ((hT.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop (0 : ℝ))).exists
    refine ⟨z, hz0, ?_⟩
    unfold qL
    have hJ0 : 0 ≤ ∫ d, max (d - z) 0 ∂D := integral_nonneg fun d => le_max_right _ _
    have hpJ : 0 ≤ K.p * ∫ d, max (d - z) 0 ∂D := mul_nonneg K.p_nonneg hJ0
    have h1 : ∫ ds, q0 K D (yAfter L (Fin.snoc (α := fun _ => ℝ) x z) ds) ∂(Measure.pi fun _ : Fin L => D)
        ≤ ∫ ds : Fin L → ℝ, K.p * ∫ d, max (d - z) 0 ∂D ∂(Measure.pi fun _ : Fin L => D) := by
      refine integral_mono (int_q0y K D hmean L _) (integrable_const _) fun ds => ?_
      have hy := yAfter_ge_last L hL (Fin.snoc (α := fun _ => ℝ) x z) ds
      simp only [Fin.snoc_last] at hy
      unfold q0
      rw [hc, hh0]
      simp only [zero_mul, zero_add]
      refine mul_le_mul_of_nonneg_left ?_ K.p_nonneg
      exact integral_mono (int_max2 D hmean _) (int_max2 D hmean _) fun d => by
        simp only
        exact max_le_max (by linarith) le_rfl
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
    have hγL : K.γ ^ L ≤ 1 := pow_le_one₀ K.γ_nonneg K.γ_lt_one.le
    calc K.γ ^ L * _ ≤ K.γ ^ L * (K.p * ∫ d, max (d - z) 0 ∂D) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg K.γ_nonneg L)
      _ ≤ 1 * (K.p * ∫ d, max (d - z) 0 ∂D) := mul_le_mul_of_nonneg_right hγL hpJ
      _ ≤ ε := by linarith
  · refine ⟨0, le_rfl, ?_⟩
    unfold qL
    rw [hγ, zero_pow (by omega)]
    simpa using hε.le

lemma fH_small (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L)
    (hB : (K.c = 0 ∧ K.hhat = 0) ∨ K.γ = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ n, ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fH K D L n x ≤ ENNReal.ofReal (ε / (1 - K.γ)) := by
  have h1 : 0 < 1 - K.γ := by linarith [K.γ_lt_one]
  intro n
  induction n with
  | zero => intro x _; simp [fH]
  | succ n ih =>
    intro x hx
    obtain ⟨z, hz0, hz⟩ := small_q K D hD hmean L hL hB x ε hε
    show bellman K D L (fH K D L n) x ≤ _
    rw [bellman_def]
    refine (iInf₂_le z hz0).trans ?_
    unfold GG
    have h2 : ∫⁻ d, fH K D L n (next x z d) ∂D ≤ ENNReal.ofReal (ε / (1 - K.γ)) := by
      calc _ ≤ ∫⁻ d, ENNReal.ofReal (ε / (1 - K.γ)) ∂D :=
            lintegral_mono fun d => ih _ (next_nonneg x z d hx hz0)
        _ = _ := by simp
    calc _ ≤ ENNReal.ofReal ε + ENNReal.ofReal K.γ * ENNReal.ofReal (ε / (1 - K.γ)) := by
          gcongr
      _ = ENNReal.ofReal (ε / (1 - K.γ)) := by
          rw [← ENNReal.ofReal_mul K.γ_nonneg, ← ENNReal.ofReal_add hε.le (mul_nonneg K.γ_nonneg (div_nonneg hε.le h1.le))]
          congr 1
          field_simp
          ring

lemma fStar_zero_B (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L)
    (hB : (K.c = 0 ∧ K.hhat = 0) ∨ K.γ = 0) (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) :
    fStar K D L x = 0 := by
  have h1 : 0 < 1 - K.γ := by linarith [K.γ_lt_one]
  apply ennreal_eq_zero_of_forall
  intro δ hδ
  have := fH_small K D hD hmean L hL hB (δ * (1 - K.γ)) (by positivity)
  have e : δ * (1 - K.γ) / (1 - K.γ) = δ := by field_simp
  rw [e] at this
  exact iSup_le fun n => this n x hx

lemma bellman_zero_B (hD : LostSalesOldNew.StateReduction.IsDemand D)
    (hmean : Integrable (fun d : ℝ => d) D) (L : ℕ) (hL : 1 ≤ L)
    (hB : (K.c = 0 ∧ K.hhat = 0) ∨ K.γ = 0) (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) :
    bellman K D L (fStar K D L) x = 0 := by
  apply ennreal_eq_zero_of_forall
  intro δ hδ
  obtain ⟨z, hz0, hz⟩ := small_q K D hD hmean L hL hB x δ hδ
  rw [bellman_def]
  refine (iInf₂_le z hz0).trans ?_
  unfold GG
  have : ∫⁻ d, fStar K D L (next x z d) ∂D = 0 := by
    rw [lintegral_congr (g := fun _ => 0) fun d => fStar_zero_B K D hD hmean L hL hB _ (next_nonneg x z d hx hz0)]
    simp
  rw [this]
  simpa using ENNReal.ofReal_le_ofReal hz

end DP


lemma kappa_pos (K : Costs) (hγ : 0 < K.γ) (h : 0 < K.c ∨ 0 < K.hhat) : 0 < K.c + K.h := by
  unfold Costs.h
  have := K.hhat_nonneg; have := K.c_nonneg; have := K.γ_lt_one
  rcases h with h | h <;> nlinarith

theorem optimality_core (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (L : ℕ) (hL : 1 ≤ L) :
    (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x = bellman K D L (fStar K D L) x) ∧
    ((0 < K.c ∨ 0 < K.hhat) → ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → ∃ z : ℝ, 0 ≤ z ∧
      fStar K D L x = ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
        + ENNReal.ofReal K.γ * ∫⁻ d, fStar K D L (LostSalesOldNew.StateReduction.next x z d) ∂D) ∧
    (∀ g : (Fin L → ℝ) → ENNReal,
      (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → g x = bellman K D L g x) →
      ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x ≤ g x) := by
  refine ⟨fun x hx => ?_, fun h x hx => ?_, fun g hg => fStar_le_of_fix K D L g hg⟩
  · by_cases hB : (K.c = 0 ∧ K.hhat = 0) ∨ K.γ = 0
    · rw [fStar_zero_B K D hD hmean L hL hB x hx, bellman_zero_B K D hD hmean L hL hB x hx]
    · have hγ : 0 < K.γ := lt_of_le_of_ne K.γ_nonneg (fun h => hB (Or.inr h.symm))
      have hc : 0 < K.c ∨ 0 < K.hhat := by
        by_contra hcon
        push_neg at hcon
        exact hB (Or.inl ⟨le_antisymm hcon.1 K.c_nonneg, le_antisymm hcon.2 K.hhat_nonneg⟩)
      exact (main_A K D hD hmean L hL hγ (kappa_pos K hγ hc) x).1
  · by_cases hγ0 : K.γ = 0
    · refine ⟨0, le_rfl, ?_⟩
      rw [fStar_zero_B K D hD hmean L hL (Or.inr hγ0) x hx]
      have : qL K D L (Fin.snoc (α := fun _ => ℝ) x 0) = 0 := by
        unfold qL
        rw [hγ0, zero_pow (by omega)]
        simp
      rw [this, hγ0]
      simp
    · have hγ : 0 < K.γ := lt_of_le_of_ne K.γ_nonneg (Ne.symm hγ0)
      exact (main_A K D hD hmean L hL hγ (kappa_pos K hγ h) x).2

end LostSalesOldNew.LeadTime

open LostSalesOldNew.LeadTime
open MeasureTheory

theorem solution (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (L : ℕ) (hL : 1 ≤ L) :
    (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x = bellman K D L (fStar K D L) x) ∧
    ((0 < K.c ∨ 0 < K.hhat) → ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → ∃ z : ℝ, 0 ≤ z ∧
      fStar K D L x = ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
        + ENNReal.ofReal K.γ * ∫⁻ d, fStar K D L (LostSalesOldNew.StateReduction.next x z d) ∂D) ∧
    (∀ g : (Fin L → ℝ) → ENNReal,
      (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → g x = bellman K D L g x) →
      ∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → fStar K D L x ≤ g x) := by
  exact optimality_core K D hD hmean L hL
