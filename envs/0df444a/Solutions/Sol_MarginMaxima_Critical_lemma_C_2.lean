-- Prove2me | solution 1 for MarginMaxima.Critical.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T01:31:39.809347+00:00
-- url     : https://prove2.me/submissions/ed9aa988-8191-438d-9be9-a6f19f72af86

import Mathlib

open MeasureTheory

namespace MarginMaxima.Critical

variable {D : ℕ}

lemma gauss_int (b : ℝ) (hb : 0 < b) :
    Integrable (fun g : EuclideanSpace ℝ (Fin D) => Real.exp (-b * ‖g‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin D)) (b := (b : ℂ)) (by simpa using hb) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun g => ?_)
  simp [Complex.norm_exp]
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma gauss_pos (b : ℝ) (hb : 0 < b) :
    0 < ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]; positivity

lemma int_bdd {f Q : EuclideanSpace ℝ (Fin D) → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 ≤ f g)
    (h1 : ∀ g, f g ≤ 1) (hQ : Integrable Q) (hQ0 : ∀ g, 0 ≤ Q g) :
    Integrable (fun g => f g * Q g) := by
  refine hQ.mono' (hf.aestronglyMeasurable.mul hQ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 g) (hQ0 g))]
  nlinarith [h0 g, h1 g, hQ0 g]

lemma mgf_pt (b : ℝ) (hb : 0 < b) (x g : EuclideanSpace ℝ (Fin D)) (l : ℝ) :
    Real.exp (l * inner ℝ g x) * Real.exp (-b * ‖g‖ ^ 2) =
      Real.exp (l ^ 2 * ‖x‖ ^ 2 / (4 * b)) *
        Real.exp (-b * ‖g - (l / (2 * b)) • x‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

lemma mgf_int (b : ℝ) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin D)) (l : ℝ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin D) =>
      Real.exp (l * inner ℝ g x) * Real.exp (-b * ‖g‖ ^ 2)) := by
  simp_rw [mgf_pt b hb x _ l]
  exact ((gauss_int b hb).comp_sub_right ((l / (2 * b)) • x)).const_mul _

lemma mgf_val (b : ℝ) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin D)) (l : ℝ) :
    ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (l * inner ℝ g x) * Real.exp (-b * ‖g‖ ^ 2) =
      Real.exp (l ^ 2 * ‖x‖ ^ 2 / (4 * b)) *
        ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2) := by
  simp_rw [mgf_pt b hb x _ l]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun g : EuclideanSpace ℝ (Fin D) => Real.exp (-b * ‖g‖ ^ 2))
    ((l / (2 * b)) • x)

lemma meas_ind (x : EuclideanSpace ℝ (Fin D)) (s : ℝ) :
    Measurable (fun g : EuclideanSpace ℝ (Fin D) => if s < |inner ℝ g x| then (1 : ℝ) else 0) := by
  refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
  exact (continuous_abs.comp (continuous_id.inner continuous_const)).measurable

lemma chernoff (b : ℝ) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin D)) (hx : ‖x‖ ≤ 1) (s : ℝ)
    (hs : 0 ≤ s) :
    ∫ g : EuclideanSpace ℝ (Fin D), (if s < |inner ℝ g x| then (1 : ℝ) else 0) *
        Real.exp (-b * ‖g‖ ^ 2) ≤
      2 * Real.exp (-b * s ^ 2) * ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2) := by
  set P : EuclideanSpace ℝ (Fin D) → ℝ := fun g => Real.exp (-b * ‖g‖ ^ 2) with hP
  have hP0 : ∀ g, 0 ≤ P g := fun g => (Real.exp_pos _).le
  have hint := int_bdd (meas_ind x s) (fun g => by split_ifs <;> norm_num)
    (fun g => by split_ifs <;> norm_num) (gauss_int b hb) hP0
  have h1 := mgf_int b hb x (2 * b * s)
  have h2 := mgf_int b hb x (-(2 * b * s))
  have hle : ∫ g : EuclideanSpace ℝ (Fin D), (if s < |inner ℝ g x| then (1 : ℝ) else 0) * P g ≤
      ∫ g : EuclideanSpace ℝ (Fin D),
        (Real.exp (-(2 * b * s ^ 2)) * (Real.exp (2 * b * s * inner ℝ g x) * P g) +
         Real.exp (-(2 * b * s ^ 2)) * (Real.exp (-(2 * b * s) * inner ℝ g x) * P g)) := by
    refine integral_mono hint ((h1.const_mul _).add (h2.const_mul _)) fun g => ?_
    dsimp only
    have hPg := hP0 g
    have e1 : Real.exp (-(2 * b * s ^ 2)) * Real.exp (2 * b * s * inner ℝ g x) =
        Real.exp (2 * b * s * (inner ℝ g x - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(2 * b * s ^ 2)) * Real.exp (-(2 * b * s) * inner ℝ g x) =
        Real.exp (2 * b * s * (-inner ℝ g x - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← mul_assoc, ← mul_assoc, e1, e2, ← add_mul]
    split_ifs with h
    · rw [one_mul]
      refine le_mul_of_one_le_left hPg ?_
      have hs' : 0 ≤ 2 * b * s := by positivity
      rcases lt_abs.mp h with h | h
      · have : 1 ≤ Real.exp (2 * b * s * (inner ℝ g x - s)) :=
          Real.one_le_exp (mul_nonneg hs' (by linarith))
        linarith [Real.exp_pos (2 * b * s * (-inner ℝ g x - s))]
      · have : 1 ≤ Real.exp (2 * b * s * (-inner ℝ g x - s)) :=
          Real.one_le_exp (mul_nonneg hs' (by linarith))
        linarith [Real.exp_pos (2 * b * s * (inner ℝ g x - s))]
    · rw [zero_mul]; positivity
  refine hle.trans ?_
  rw [integral_add ((h1.const_mul _)) ((h2.const_mul _)), integral_const_mul, integral_const_mul,
    mgf_val b hb x, mgf_val b hb x]
  have hZ := gauss_pos (D := D) b hb
  have k : Real.exp (-(2 * b * s ^ 2)) * Real.exp ((2 * b * s) ^ 2 * ‖x‖ ^ 2 / (4 * b)) ≤
      Real.exp (-b * s ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have : (2 * b * s) ^ 2 * ‖x‖ ^ 2 / (4 * b) ≤ b * s ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hb.le hb.le) (sq_nonneg s)]
    linarith
  have k2 : Real.exp (-(2 * b * s ^ 2)) * Real.exp ((-(2 * b * s)) ^ 2 * ‖x‖ ^ 2 / (4 * b)) ≤
      Real.exp (-b * s ^ 2) := by
    rw [neg_sq]; exact k
  nlinarith [mul_le_mul_of_nonneg_right k hZ.le, mul_le_mul_of_nonneg_right k2 hZ.le]


noncomputable def cnt {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s : ℝ)
    (g : EuclideanSpace ℝ (Fin D)) : ℝ :=
  ∑ i, if s < |inner ℝ g (x i)| then (1 : ℝ) else 0

lemma cnt_eq {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s : ℝ)
    (g : EuclideanSpace ℝ (Fin D)) :
    cnt x s g = ((Finset.univ.filter fun i => s < |inner ℝ g (x i)|).card : ℝ) := by
  unfold cnt
  rw [Finset.sum_boole]

lemma cnt_meas {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s : ℝ) :
    Measurable (cnt x s) := by
  unfold cnt
  exact Finset.measurable_sum _ (fun i _ => meas_ind (x i) s)

lemma cnt_nonneg {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s : ℝ)
    (g : EuclideanSpace ℝ (Fin D)) : 0 ≤ cnt x s g := by
  unfold cnt
  exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cnt_neg {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s : ℝ)
    (g : EuclideanSpace ℝ (Fin D)) : cnt x s (-g) = cnt x s g := by
  unfold cnt
  simp [inner_neg_left]

lemma cnt_int {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s b : ℝ) (hb : 0 < b) :
    Integrable (fun g => cnt x s g * Real.exp (-b * ‖g‖ ^ 2)) := by
  unfold cnt
  simp_rw [Finset.sum_mul]
  refine integrable_finset_sum _ (fun i _ => ?_)
  exact int_bdd (meas_ind (x i) s) (fun g => by split_ifs <;> norm_num)
    (fun g => by split_ifs <;> norm_num) (gauss_int b hb) (fun g => (Real.exp_pos _).le)

lemma tail_bound {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (hx : ∀ i, ‖x i‖ ≤ 1)
    (t δ : ℝ) (ht : 0 < t) (hδ0 : 0 < δ) (b : ℝ) (hb : b = 4 * Real.log (8 / δ) / t ^ 2)
    (hb0 : 0 < b) :
    ∫ g : EuclideanSpace ℝ (Fin D), cnt x (t / 2) g * Real.exp (-b * ‖g‖ ^ 2) ≤
      m * (δ / 4) * ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2) := by
  unfold cnt
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => ?_)]
  swap
  · exact int_bdd (meas_ind (x i) (t / 2)) (fun g => by split_ifs <;> norm_num)
      (fun g => by split_ifs <;> norm_num) (gauss_int b hb0) (fun g => (Real.exp_pos _).le)
  have hk : 2 * Real.exp (-b * (t / 2) ^ 2) = δ / 4 := by
    have : -b * (t / 2) ^ 2 = -Real.log (8 / δ) := by
      rw [hb]; field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp; norm_num
  have hZ := gauss_pos (D := D) b hb0
  calc _ ≤ ∑ i : Fin m, (δ / 4) * ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := chernoff b hb0 (x i) (hx i) (t / 2) (by positivity)
        rwa [hk] at this
    _ = _ := by simp [mul_assoc]

lemma lowerA {m : ℕ} (hm : 0 < m) (x : Fin m → EuclideanSpace ℝ (Fin D))
    (hx : ∀ i, ‖x i‖ ≤ 1) (t δ : ℝ) (ht : 0 < t) (hδ0 : 0 < δ) (b : ℝ)
    (hb : b = 4 * Real.log (8 / δ) / t ^ 2) (hb0 : 0 < b) :
    (∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2)) / 2 ≤
      ∫ g : EuclideanSpace ℝ (Fin D),
        (if cnt x (t / 2) g ≤ δ * m / 2 then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2) := by
  have hZ := gauss_pos (D := D) b hb0
  have htail := tail_bound x hx t δ ht hδ0 b hb hb0
  have hint := int_bdd (f := fun g => if cnt x (t / 2) g ≤ δ * m / 2 then (1 : ℝ) else 0)
    (Measurable.ite (measurableSet_le (cnt_meas x _) measurable_const) measurable_const
      measurable_const) (fun g => by split_ifs <;> norm_num)
    (fun g => by split_ifs <;> norm_num) (gauss_int (D := D) b hb0)
    (fun g => (Real.exp_pos _).le)
  have hmono : ∫ g : EuclideanSpace ℝ (Fin D), (δ * m / 2) *
      (Real.exp (-b * ‖g‖ ^ 2) -
        (if cnt x (t / 2) g ≤ δ * m / 2 then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2)) ≤
      ∫ g : EuclideanSpace ℝ (Fin D), cnt x (t / 2) g * Real.exp (-b * ‖g‖ ^ 2) := by
    refine integral_mono (((gauss_int b hb0).sub hint).const_mul _) (cnt_int x _ b hb0)
      (fun g => ?_)
    have hP := (Real.exp_pos (-b * ‖g‖ ^ 2)).le
    by_cases h : cnt x (t / 2) g ≤ δ * m / 2
    · rw [if_pos h]; simp only [one_mul, sub_self, mul_zero]
      exact mul_nonneg (cnt_nonneg x _ g) hP
    · rw [if_neg h]; push_neg at h
      simp only [zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_right h.le hP
  rw [integral_const_mul, integral_sub (gauss_int b hb0) hint] at hmono
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < δ * m / 2 := by positivity
  have h3 := hmono.trans htail
  have h4 : δ * m / 2 * ((∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2)) -
      (∫ g : EuclideanSpace ℝ (Fin D),
        (if cnt x (t / 2) g ≤ δ * m / 2 then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2))) ≤
      δ * m / 2 * ((∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2)) / 2) := by
    refine h3.trans (le_of_eq ?_); ring
  have := le_of_mul_le_mul_left h4 hpos
  linarith

lemma shift_lower {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (s c b : ℝ) (hb0 : 0 < b)
    (u : EuclideanSpace ℝ (Fin D)) :
    Real.exp (-b * ‖u‖ ^ 2) * ∫ g : EuclideanSpace ℝ (Fin D),
        (if cnt x s g ≤ c then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2) ≤
      ∫ g : EuclideanSpace ℝ (Fin D),
        (if cnt x s (g - u) ≤ c then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2) := by
  set f : EuclideanSpace ℝ (Fin D) → ℝ := fun g => if cnt x s g ≤ c then (1 : ℝ) else 0 with hf
  have hfm : Measurable f :=
    Measurable.ite (measurableSet_le (cnt_meas x _) measurable_const) measurable_const
      measurable_const
  have hf0 : ∀ g, 0 ≤ f g := fun g => by simp only [hf]; split_ifs <;> norm_num
  have hf1 : ∀ g, f g ≤ 1 := fun g => by simp only [hf]; split_ifs <;> norm_num
  have hfneg : ∀ g, f (-g) = f g := fun g => by simp only [hf, cnt_neg]
  have hP0 : ∀ g : EuclideanSpace ℝ (Fin D), 0 ≤ Real.exp (-b * ‖g‖ ^ 2) :=
    fun g => (Real.exp_pos _).le
  set P : EuclideanSpace ℝ (Fin D) → ℝ := fun g => Real.exp (-b * ‖g‖ ^ 2) with hP
  have hPi : Integrable P := gauss_int b hb0
  -- shift
  have e1 : ∫ g, f (g - u) * P g = ∫ h, f h * P (h + u) := by
    rw [← integral_add_right_eq_self (fun g => f (g - u) * P g) u]
    simp
  have i1 : Integrable (fun h => f h * P (h + u)) :=
    int_bdd hfm hf0 hf1 (hPi.comp_add_right u) (fun g => hP0 _)
  have i2 : Integrable (fun h => f h * P (u - h)) := by
    have : Integrable (fun h => f h * P (-h + u)) := by
      have := (hPi.comp_add_right u).comp_neg
      exact int_bdd hfm hf0 hf1 this (fun g => hP0 _)
    simpa [sub_eq_add_neg, add_comm] using this
  have e2 : ∫ h, f h * P (h + u) = ∫ h, f h * P (u - h) := by
    rw [← integral_neg_eq_self (fun h => f h * P (h + u))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp [hfneg, sub_eq_add_neg, add_comm]
  have i3 : Integrable (fun h => f h * P h) := int_bdd hfm hf0 hf1 hPi hP0
  have hpt : ∀ h, 2 * (Real.exp (-b * ‖u‖ ^ 2) * (f h * P h)) ≤
      f h * P (h + u) + f h * P (u - h) := by
    intro h
    have a1 : P (h + u) = P h * Real.exp (-b * ‖u‖ ^ 2) * Real.exp (-(2 * b * inner ℝ h u)) := by
      simp only [hP]; rw [← Real.exp_add, ← Real.exp_add, norm_add_sq_real]; congr 1; ring
    have a2 : P (u - h) = P h * Real.exp (-b * ‖u‖ ^ 2) * Real.exp (2 * b * inner ℝ h u) := by
      simp only [hP]; rw [← Real.exp_add, ← Real.exp_add, norm_sub_sq_real, real_inner_comm]
      congr 1; ring
    have k1 := Real.add_one_le_exp (-(2 * b * inner ℝ h u))
    have k2 := Real.add_one_le_exp (2 * b * inner ℝ h u)
    have hq : 0 ≤ f h * (P h * Real.exp (-b * ‖u‖ ^ 2)) :=
      mul_nonneg (hf0 h) (mul_nonneg (hP0 h) (Real.exp_pos _).le)
    rw [a1, a2]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (2:ℝ) ≤ Real.exp (-(2 * b * inner ℝ h u)) +
      Real.exp (2 * b * inner ℝ h u)) hq]
  have hI := integral_mono ((i3.const_mul (Real.exp (-b * ‖u‖ ^ 2))).const_mul 2) (i1.add i2) hpt
  have hadd := integral_add i1 i2
  rw [integral_const_mul, integral_const_mul] at hI
  simp only [Pi.add_apply] at hI
  rw [hadd, ← e2, ← e1] at hI
  have : ∫ g, f (g - u) * P g = ∫ g, (if cnt x s (g - u) ≤ c then (1 : ℝ) else 0) *
      Real.exp (-b * ‖g‖ ^ 2) := rfl
  linarith


lemma pair_disjoint {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (t δ : ℝ)
    (u v g : EuclideanSpace ℝ (Fin D))
    (hs : δ * m < ((Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|).card : ℝ))
    (hu : cnt x (t / 2) (g - u) ≤ δ * m / 2) (hv : cnt x (t / 2) (g - v) ≤ δ * m / 2) :
    False := by
  rw [cnt_eq] at hu hv
  have hsub : (Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|) ⊆
      (Finset.univ.filter fun i => t / 2 < |inner ℝ (g - u) (x i)|) ∪
      (Finset.univ.filter fun i => t / 2 < |inner ℝ (g - v) (x i)|) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_contra hc
    push Not at hc
    have : u - v = (g - v) - (g - u) := by abel
    rw [this, inner_sub_left] at hi
    have := abs_sub (inner ℝ (g - v) (x i)) (inner ℝ (g - u) (x i))
    linarith [hc.1, hc.2]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter fun i => t / 2 < |inner ℝ (g - u) (x i)|)
    (Finset.univ.filter fun i => t / 2 < |inner ℝ (g - v) (x i)|)
  have h3 : ((Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|).card : ℝ) ≤
      ((Finset.univ.filter fun i => t / 2 < |inner ℝ (g - u) (x i)|).card : ℝ) +
      ((Finset.univ.filter fun i => t / 2 < |inner ℝ (g - v) (x i)|).card : ℝ) := by
    exact_mod_cast h1.trans h2
  linarith

lemma sum_ind_le_one {m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin D)) (t δ : ℝ)
    (F : Finset (EuclideanSpace ℝ (Fin D)))
    (hs : ∀ u ∈ F, ∀ v ∈ F, u ≠ v →
      δ * m < ((Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|).card : ℝ))
    (g : EuclideanSpace ℝ (Fin D)) :
    ∑ u ∈ F, (if cnt x (t / 2) (g - u) ≤ δ * m / 2 then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ u ∈ F, cnt x (t / 2) (g - u) ≤ δ * m / 2
  · obtain ⟨u, hu, hu'⟩ := h
    rw [Finset.sum_eq_single u]
    · rw [if_pos hu']
    · intro v hv hvu
      rw [if_neg]
      intro hv'
      exact pair_disjoint x t δ v u g (hs v hv u hu hvu) hv' hu'
    · intro h; exact absurd hu h
  · push Not at h
    rw [Finset.sum_eq_zero]
    · norm_num
    · intro u hu; rw [if_neg (not_le.mpr (h u hu))]

lemma finset_bound {m : ℕ} (hm : 0 < m) (x : Fin m → EuclideanSpace ℝ (Fin D))
    (hx : ∀ i, ‖x i‖ ≤ 1) (t ρ δ : ℝ) (ht : 0 < t) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (F : Finset (EuclideanSpace ℝ (Fin D))) (hF : ∀ u ∈ F, ‖u‖ ≤ ρ)
    (hs : ∀ u ∈ F, ∀ v ∈ F, u ≠ v →
      δ * m < ((Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|).card : ℝ)) :
    (F.card : ℝ) ≤ 2 * Real.exp (4 * ρ ^ 2 * Real.log (8 / δ) / t ^ 2) := by
  set L := Real.log (8 / δ) with hL
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set b := 4 * L / t ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hZ := gauss_pos (D := D) b hb0
  set Z := ∫ g : EuclideanSpace ℝ (Fin D), Real.exp (-b * ‖g‖ ^ 2) with hZdef
  have hlow := lowerA hm x hx t δ ht hδ0 b hb hb0
  have hfm : ∀ u : EuclideanSpace ℝ (Fin D), Measurable
      (fun g => if cnt x (t / 2) (g - u) ≤ δ * m / 2 then (1 : ℝ) else 0) := fun u =>
    Measurable.ite (measurableSet_le ((cnt_meas x _).comp (measurable_id.sub_const u))
      measurable_const) measurable_const measurable_const
  have hint : ∀ u ∈ F, Integrable (fun g : EuclideanSpace ℝ (Fin D) =>
      (if cnt x (t / 2) (g - u) ≤ δ * m / 2 then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2)) :=
    fun u _ => int_bdd (hfm u) (fun g => by split_ifs <;> norm_num)
      (fun g => by split_ifs <;> norm_num) (gauss_int b hb0) (fun g => (Real.exp_pos _).le)
  have hsum : ∑ u ∈ F, ∫ g : EuclideanSpace ℝ (Fin D),
      (if cnt x (t / 2) (g - u) ≤ δ * m / 2 then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2) ≤ Z := by
    rw [← integral_finset_sum _ hint]
    refine integral_mono (integrable_finset_sum _ hint) (gauss_int b hb0) (fun g => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (sum_ind_le_one x t δ F hs g)
  have hterm : ∀ u ∈ F, Real.exp (-b * ρ ^ 2) * (Z / 2) ≤ ∫ g : EuclideanSpace ℝ (Fin D),
      (if cnt x (t / 2) (g - u) ≤ δ * m / 2 then (1 : ℝ) else 0) * Real.exp (-b * ‖g‖ ^ 2) := by
    intro u hu
    refine le_trans ?_ (shift_lower x (t / 2) (δ * m / 2) b hb0 u)
    have h1 : Real.exp (-b * ρ ^ 2) ≤ Real.exp (-b * ‖u‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := hF u hu
      have h2 : ‖u‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [mul_le_mul_of_nonneg_left h2 hb0.le]
    exact mul_le_mul h1 hlow (by positivity) (Real.exp_pos _).le
  have h2 := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : (F.card : ℝ) * (Real.exp (-b * ρ ^ 2) * (Z / 2)) ≤ Z := h2.trans hsum
  have h4 : Real.exp (-b * ρ ^ 2) * Real.exp (b * ρ ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h5 : (F.card : ℝ) ≤ 2 * Real.exp (b * ρ ^ 2) := by
    have hE := Real.exp_pos (b * ρ ^ 2)
    have hE' := Real.exp_pos (-b * ρ ^ 2)
    by_contra hc
    push Not at hc
    have : 2 * Real.exp (b * ρ ^ 2) * (Real.exp (-b * ρ ^ 2) * (Z / 2)) <
        (F.card : ℝ) * (Real.exp (-b * ρ ^ 2) * (Z / 2)) :=
      mul_lt_mul_of_pos_right hc (by positivity)
    have e : 2 * Real.exp (b * ρ ^ 2) * (Real.exp (-b * ρ ^ 2) * (Z / 2)) = Z := by
      linear_combination Z * h4
    linarith
  have : b * ρ ^ 2 = 4 * ρ ^ 2 * L / t ^ 2 := by rw [hb]; ring
  rwa [this] at h5

end MarginMaxima.Critical

open MarginMaxima.Critical in
theorem solution (D m : ℕ) (x : Fin m → EuclideanSpace ℝ (Fin D)) (hx : ∀ i, ‖x i‖ ≤ 1)
    (t ρ δ : ℝ) (ht : 0 < t) (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (U : Set (EuclideanSpace ℝ (Fin D))) (hU : U ⊆ Metric.closedBall 0 ρ)
    (hsep : ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      δ * m < ((Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|).card : ℝ)) :
    U.Finite ∧ (U.ncard : ℝ) ≤ 2 * Real.exp (4 * ρ ^ 2 * Real.log (8 / δ) / t ^ 2) := by
  set K := 2 * Real.exp (4 * ρ ^ 2 * Real.log (8 / δ) / t ^ 2) with hK
  have hL0 : 0 ≤ Real.log (8 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hK2 : 2 ≤ K := by
    have : 1 ≤ Real.exp (4 * ρ ^ 2 * Real.log (8 / δ) / t ^ 2) :=
      Real.one_le_exp (by positivity)
    rw [hK]; linarith
  have key : ∀ F : Finset (EuclideanSpace ℝ (Fin D)), (F : Set _) ⊆ U → (F.card : ℝ) ≤ K := by
    intro F hFU
    by_cases hc : F.card ≤ 1
    · have : (F.card : ℝ) ≤ 1 := by exact_mod_cast hc
      linarith
    · push Not at hc
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
      have h1 := hsep u (hFU hu) v (hFU hv) huv
      have hm : 0 < m := by
        by_contra h0
        have : m = 0 := by omega
        subst this
        have : ((Finset.univ.filter fun i : Fin 0 => t < |inner ℝ (u - v) (x i)|).card : ℝ) = 0 := by
          simp
        simp at h1
      exact finset_bound hm x hx t ρ δ ht hδ0 hδ1 F
        (fun u hu => by simpa using hU (hFU hu)) (fun u hu v hv h => hsep u (hFU hu) v (hFU hv) h)
  have hfin : U.Finite := by
    by_contra hinf
    obtain ⟨F, hFU, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈K⌉₊ + 1)
    have h1 := key F hFU
    rw [hFc] at h1
    have h2 := Nat.le_ceil K
    push_cast at h1
    linarith
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card U hfin]
  exact key _ (by simp)

