-- Prove2me | solution 1 for KalaiVempala.Multiplicative.theorem_1_1_b
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T10:40:45.890287+00:00
-- url     : https://prove2.me/submissions/56f59812-5f8f-42a0-9290-69e35e2b6af7

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_KalaiVempala_Multiplicative_Setting
import Mathlib


section

open MeasureTheory Set Filter
open scoped BigOperators

namespace KalaiVempala.Multiplicative.KVFresh

noncomputable def laplaceDensity (η x : ℝ) : ℝ :=
  (η / 2) * Real.exp (-(η * |x|))

lemma integrable_comp_abs_of_Ioi {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x => f |x|) := by
  have hp : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    apply hf.congr_fun _ measurableSet_Ioi
    intro x hx
    change f x = f |x|
    rw [abs_of_pos (show 0 < x from hx)]
  have hn : IntegrableOn (fun x => f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  have h := hn.union hp
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

lemma laplaceDensity_nonneg {η : ℝ} (hη : 0 < η) (x : ℝ) :
    0 ≤ laplaceDensity η x := by
  unfold laplaceDensity
  positivity

lemma continuous_laplaceDensity (η : ℝ) : Continuous (laplaceDensity η) := by
  unfold laplaceDensity
  fun_prop

lemma integrable_laplaceDensity {η : ℝ} (hη : 0 < η) :
    Integrable (laplaceDensity η) := by
  have h := integrable_comp_abs_of_Ioi
    (integrableOn_exp_mul_Ioi (a := -η) (by linarith) 0)
  change Integrable (fun x => (η / 2) * Real.exp (-(η * |x|)))
  simpa only [neg_mul] using h.const_mul (η / 2)

lemma integral_laplaceDensity {η : ℝ} (hη : 0 < η) :
    ∫ x, laplaceDensity η x = 1 := by
  simp only [laplaceDensity, integral_const_mul]
  rw [show (fun x : ℝ => Real.exp (-(η * |x|))) =
    (fun x => (fun y => Real.exp ((-η) * y)) |x|) by funext x; simp only [neg_mul]]
  rw [integral_comp_abs (f := fun y : ℝ => Real.exp ((-η) * y)), integral_exp_mul_Ioi (by linarith : -η < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory Set Filter
open scoped BigOperators

namespace KalaiVempala.Multiplicative.KVFresh

noncomputable def productDensity (n : ℕ) (η : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, laplaceDensity η (x i)

lemma productDensity_eq (n : ℕ) (η : ℝ) (x : Fin n → ℝ) :
    productDensity n η x = (η / 2)^n * Real.exp (-(η * ∑ i, |x i|)) := by
  simp only [productDensity, laplaceDensity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  simp only [Finset.mul_sum, Finset.sum_neg_distrib]

lemma productDensity_nonneg {n : ℕ} {η : ℝ} (hη : 0 < η) (x : Fin n → ℝ) :
    0 ≤ productDensity n η x :=
  Finset.prod_nonneg fun i _ => laplaceDensity_nonneg hη (x i)

lemma continuous_productDensity (n : ℕ) (η : ℝ) :
    Continuous (productDensity n η) := by
  unfold productDensity laplaceDensity
  fun_prop

lemma integrable_productDensity (n : ℕ) {η : ℝ} (hη : 0 < η) :
    Integrable (productDensity n η) := by
  exact Integrable.fintype_prod (fun _ : Fin n => integrable_laplaceDensity hη)

lemma integral_productDensity (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫ x, productDensity n η x = 1 := by
  unfold productDensity
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [integral_laplaceDensity hη, Finset.prod_const_one]

lemma laplaceLaw_eq_productDensity (n : ℕ) (η : ℝ) :
    laplaceLaw n η = volume.withDensity (fun x => ENNReal.ofReal (productDensity n η x)) := by
  simp only [laplaceLaw, productDensity_eq]

lemma laplaceLaw_probability (n : ℕ) {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (laplaceLaw n η) := by
  constructor
  rw [laplaceLaw_eq_productDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_productDensity n hη) (Eventually.of_forall (productDensity_nonneg hη)),
    integral_productDensity n hη, ENNReal.ofReal_one]

lemma integral_laplaceLaw (n : ℕ) {η : ℝ} (hη : 0 < η) (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂laplaceLaw n η = ∫ x, productDensity n η x * f x := by
  rw [laplaceLaw_eq_productDensity,
    integral_withDensity_eq_integral_toReal_smul
      ((continuous_productDensity n η).measurable.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (productDensity_nonneg hη _), smul_eq_mul]

lemma integrable_laplaceLaw_iff (n : ℕ) {η : ℝ} (hη : 0 < η)
    (f : (Fin n → ℝ) → ℝ) :
    Integrable f (laplaceLaw n η) ↔ Integrable (fun x => productDensity n η x * f x) := by
  rw [laplaceLaw_eq_productDensity,
    integrable_withDensity_iff_integrable_smul'
      ((continuous_productDensity n η).measurable.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (productDensity_nonneg hη _), smul_eq_mul]

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory Set Filter
open scoped BigOperators

namespace KalaiVempala.Multiplicative.KVFresh

lemma density_translation_bound {n : ℕ} {η : ℝ} (hη : 0 < η)
    (y v : Fin n → ℝ) :
    productDensity n η (y+v) ≤ Real.exp (η * ∑ i, |v i|) * productDensity n η y := by
  have hs : ∑ i, |y i| ≤ (∑ i, |(y+v) i|) + ∑ i, |v i| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := abs_sub (y i + v i) (v i)
    simpa only [add_sub_cancel_right, Pi.add_apply] using h
  have he : Real.exp (-(η * ∑ i, |(y+v) i|)) ≤
      Real.exp (η * ∑ i, |v i|) * Real.exp (-(η * ∑ i, |y i|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [productDensity_eq, productDensity_eq]
  calc
    _ ≤ (η/2)^n * (Real.exp (η * ∑ i, |v i|) *
        Real.exp (-(η * ∑ i, |y i|))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

lemma translated_integral_bound {n : ℕ} {η : ℝ} (hη : 0 < η)
    (v : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f (laplaceLaw n η))
    (hshift : Integrable (fun x => f (x-v)) (laplaceLaw n η))
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∫ x, f (x-v) ∂laplaceLaw n η) ≤
      Real.exp (η * ∑ i, |v i|) * ∫ x, f x ∂laplaceLaw n η := by
  rw [integral_laplaceLaw n hη, integral_laplaceLaw n hη]
  have heq : (∫ x, productDensity n η x * f (x-v)) =
      ∫ y, productDensity n η (y+v) * f y := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
      (fun x : Fin n → ℝ => productDensity n η x * f (x-v)) v
    simpa only [add_sub_cancel_right] using h.symm
  rw [heq, ← integral_const_mul]
  have hi := (integrable_laplaceLaw_iff n hη f).mp hf
  have hj := (integrable_laplaceLaw_iff n hη (fun x => f (x-v))).mp hshift
  have ht : Integrable (fun y => productDensity n η (y+v) * f y) := by
    have h := hj.comp_add_right v
    simpa only [add_sub_cancel_right] using h
  apply integral_mono ht (hi.const_mul _)
  intro y
  calc
    _ ≤ (Real.exp (η * ∑ i, |v i|) * productDensity n η y) * f y :=
      mul_le_mul_of_nonneg_right (density_translation_bound hη y v) (hnonneg y)
    _ = _ := by ring

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open Matrix
open scoped BigOperators

theorem diameter_nonnegative {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (D : ℝ) (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D) : 0 ≤ D := by
  simpa using hD (M 0) (hM 0).1 (M 0) (hM 0).1

theorem oracle_coordinate_bound {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (D : ℝ) (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D)
    (x : Fin n → ℝ) (i : Fin n) : |M x i| ≤ |M 0 i| + D := by
  have hi : |M x i-M 0 i| ≤ ∑ j, |M x j-M 0 j| :=
    Finset.single_le_sum (f := fun j => |M x j-M 0 j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hd := hD (M x) (hM x).1 (M 0) (hM 0).1
  have ht := abs_add_le (M x i-M 0 i) (M 0 i)
  simp only [sub_add_cancel] at ht
  linarith

theorem oracle_norm_bound {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (D : ℝ) (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D)
    (x : Fin n → ℝ) : ‖M x‖ ≤ ‖M 0‖ + D := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (diameter_nonnegative Dset M hM D hD))).mpr
  intro i
  have hc := oracle_coordinate_bound Dset M hM D hD x i
  have hi := norm_le_pi_norm (M 0) i
  simpa only [Real.norm_eq_abs] using hc.trans (add_le_add hi le_rfl)

theorem diameter_dot_bound {n : ℕ} (x y p : Fin n → ℝ) (D : ℝ)
    (hD : ∑ i, |x i-y i| ≤ D) : x ⬝ᵥ p - y ⬝ᵥ p ≤ D * ‖p‖ := by
  calc
    x ⬝ᵥ p - y ⬝ᵥ p = ∑ i, (x i-y i)*p i := by
      simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, |x i-y i| * ‖p‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hp : |p i| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm p i
      exact (le_abs_self _).trans ((by rw [abs_mul] : |(x i-y i)*p i| = |x i-y i| * |p i|).le.trans
        (mul_le_mul_of_nonneg_left hp (abs_nonneg _)))
    _ = (∑ i, |x i-y i|)*‖p‖ := (Finset.sum_mul ..).symm
    _ ≤ D*‖p‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg _)

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open MeasureTheory Matrix
open scoped BigOperators

theorem oracle_loss_measurable {n : ℕ} (M : (Fin n → ℝ) → Fin n → ℝ)
    (hM : Measurable M) (x a : Fin n → ℝ) :
    Measurable (fun p : Fin n → ℝ => a ⬝ᵥ M (x+p)) := by
  unfold dotProduct
  fun_prop

theorem oracle_loss_integrable {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (hMmeas : Measurable M) (D : ℝ)
    (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D)
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (x a : Fin n → ℝ) :
    Integrable (fun p : Fin n → ℝ => a ⬝ᵥ M (x+p)) μ := by
  unfold dotProduct
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  apply Integrable.of_bound (C := |M 0 i|+D)
  · exact ((measurable_pi_apply i).comp (hMmeas.comp (measurable_const.add measurable_id))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs] using oracle_coordinate_bound Dset M hM D hD (x+p) i

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open Matrix OracleRO.ApproxFPL
open scoped BigOperators

@[simp] theorem kv_prefix_zero {n : ℕ} (s : ℕ → Fin n → ℝ) : prefixSum s 0 = 0 := by
  simp [prefixSum]

theorem kv_prefix_succ {n : ℕ} (s : ℕ → Fin n → ℝ) (T : ℕ) :
    prefixSum s (T+1) = prefixSum s T + s (T+1) := by
  exact Finset.sum_Icc_succ_top (by omega) s

theorem be_the_leader_perturbed {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (s : ℕ → Fin n → ℝ) (p : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t+p) ⬝ᵥ s t ≤
      M (prefixSum s T+p) ⬝ᵥ (prefixSum s T+p) - M p ⬝ᵥ p := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hm := (hM (prefixSum s T+p)).2
      (M (prefixSum s (T+1)+p)) (hM (prefixSum s (T+1)+p)).1
    have he : M (prefixSum s (T+1)+p) ⬝ᵥ (prefixSum s (T+1)+p) =
        M (prefixSum s (T+1)+p) ⬝ᵥ (prefixSum s T+p) +
          M (prefixSum s (T+1)+p) ⬝ᵥ s (T+1) := by
      conv_lhs => arg 2; rw [kv_prefix_succ, add_right_comm]
      rw [dotProduct_add]
    linarith

theorem shared_perturbation_bound {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (D : ℝ) (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (p : Fin n → ℝ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t+p) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T + D*‖p‖ := by
  have hb := be_the_leader_perturbed Dset M hM s p T
  have hm := (hM (prefixSum s T+p)).2 (M (prefixSum s T)) (hM (prefixSum s T)).1
  simp_rw [dotProduct_add] at hb hm
  have hd := diameter_dot_bound (M (prefixSum s T)) (M p) p D
    (hD _ (hM _).1 _ (hM _).1)
  linarith

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory Matrix OracleRO.ApproxFPL
open scoped BigOperators

namespace KalaiVempala.Multiplicative.KVFresh

lemma native_period_shift {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (hMmeas : Measurable M) (D : ℝ)
    (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i-d' i| ≤ D)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i)
    (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (s : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) (hs : s t ∈ S)
    {η : ℝ} (hη : 0 < η) :
    (∫ p, s t ⬝ᵥ M (prefixSum s (t-1)+p) ∂laplaceLaw n η) ≤
      Real.exp (η*A) * ∫ p, s t ⬝ᵥ M (prefixSum s t+p) ∂laplaceLaw n η := by
  let := laplaceLaw_probability n hη
  let f : (Fin n → ℝ) → ℝ := fun p => s t ⬝ᵥ M (prefixSum s t+p)
  have hp : prefixSum s t = prefixSum s (t-1)+s t := by
    have he : t-1+1=t := by omega
    simpa only [he] using kv_prefix_succ s (t-1)
  have hf := oracle_loss_integrable Dset M hM hMmeas D hD (laplaceLaw n η)
    (prefixSum s t) (s t)
  have heq : (fun x => f (x-s t)) =
      (fun x => s t ⬝ᵥ M (prefixSum s (t-1)+x)) := by
    funext x
    dsimp [f]
    rw [hp]
    congr 2
    abel
  have hj : Integrable (fun x => f (x-s t)) (laplaceLaw n η) := by
    rw [heq]
    exact oracle_loss_integrable Dset M hM hMmeas D hD (laplaceLaw n η)
      (prefixSum s (t-1)) (s t)
  have hn : ∀ x, 0 ≤ f x := by
    intro x
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hSnn _ hs i) (hDnn _ (hM _).1 i)
  have hb := translated_integral_bound hη (s t) f hf hj hn
  rw [heq] at hb
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hA _ hs) hη.le
  · exact integral_nonneg hn

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory Set Filter
open scoped BigOperators

namespace KalaiVempala.Multiplicative.KVFresh

lemma coordinate_product_identity {n : ℕ} (η : ℝ) (i : Fin n) (f : ℝ → ℝ)
    (x : Fin n → ℝ) :
    productDensity n η x * f (x i) =
      ∏ j, (if j = i then laplaceDensity η (x j) * f (x j)
        else laplaceDensity η (x j)) := by
  classical
  have h : ∀ j : Fin n, (if j = i then laplaceDensity η (x j) * f (x j)
      else laplaceDensity η (x j)) =
      laplaceDensity η (x j) * (if j = i then f (x j) else 1) := by
    intro j
    split_ifs <;> simp
  simp only [h, Finset.prod_mul_distrib, productDensity]
  simp

lemma integrable_coordinate_laplace {n : ℕ} {η : ℝ} (hη : 0 < η)
    (i : Fin n) (f : ℝ → ℝ) (hf : Integrable (fun x => laplaceDensity η x * f x)) :
    Integrable (fun x : Fin n → ℝ => f (x i)) (laplaceLaw n η) := by
  classical
  rw [integrable_laplaceLaw_iff n hη]
  simp_rw [coordinate_product_identity η i f]
  have hi : ∀ j : Fin n, Integrable
      (fun x : ℝ => if j = i then laplaceDensity η x * f x else laplaceDensity η x) := by
    intro j
    by_cases hj : j = i
    · simpa only [hj, if_true] using hf
    · simpa only [hj, if_false] using integrable_laplaceDensity hη
  exact Integrable.fintype_prod hi

lemma integral_coordinate_laplace {n : ℕ} {η : ℝ} (hη : 0 < η)
    (i : Fin n) (f : ℝ → ℝ) :
    (∫ x : Fin n → ℝ, f (x i) ∂laplaceLaw n η) =
      ∫ x : ℝ, laplaceDensity η x * f x := by
  classical
  rw [integral_laplaceLaw n hη]
  simp_rw [coordinate_product_identity η i f]
  rw [integral_fintype_prod_volume_eq_prod
    (fun j : Fin n => fun x : ℝ => if j = i then laplaceDensity η x * f x else laplaceDensity η x)]
  have h : ∀ j : Fin n,
      (∫ x : ℝ, if j = i then laplaceDensity η x * f x else laplaceDensity η x) =
      (if j = i then ∫ x : ℝ, laplaceDensity η x * f x else 1) := by
    intro j
    by_cases hj : j = i
    · simp only [hj, if_true]
    · simp only [hj, if_false, integral_laplaceDensity hη]
  simp only [h]
  simp

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory Set Filter
open scoped Topology

namespace KalaiVempala.Multiplicative.KVFresh

lemma exponential_residual_tail {η : ℝ} (hη : 0 < η) (a : ℝ) :
    IntegrableOn (fun x : ℝ => (x-a) * Real.exp (-(η*x))) (Ioi a) ∧
    (∫ x : ℝ in Ioi a, (x-a) * Real.exp (-(η*x))) =
      Real.exp (-(η*a)) / η^2 := by
  let g : ℝ → ℝ := fun x => -((x-a)/η + 1/η^2) * Real.exp (-(η*x))
  have hd : ∀ x ∈ Ici a, HasDerivAt g ((x-a) * Real.exp (-(η*x))) x := by
    intro x _
    have h := ((((hasDerivAt_id x).sub_const a).div_const η).add_const (1/η^2)).neg.mul
      (((hasDerivAt_id x).const_mul η).neg.exp)
    convert! h using 1
    dsimp only [Pi.neg_apply, Pi.mul_apply, id_eq]
    field_simp
    ring
  have hp : ∀ x ∈ Ioi a, 0 ≤ (x-a) * Real.exp (-(η*x)) := by
    intro x hx
    exact mul_nonneg (sub_nonneg.mpr hx.le) (Real.exp_pos _).le
  have he : Tendsto (fun x : ℝ => Real.exp (-(η*x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hη))
  have hxe : Tendsto (fun x : ℝ => x * Real.exp (-(η*x))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hη)
    have h' := h.div_const η
    convert h' using 1
    · funext x
      simp only [Function.comp_def, id_eq, pow_one]
      field_simp
    · simp
  have hg : Tendsto g atTop (𝓝 0) := by
    have h := ((hxe.sub (he.const_mul a)).div_const η).add (he.div_const (η^2))
    have h' := h.neg
    convert h' using 1
    · funext x
      dsimp [g]
      ring
    · simp
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp hg, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hg]
  simp only [g, sub_self, zero_div, zero_add, zero_sub, neg_mul, neg_neg]
  ring

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory Set Filter
open scoped Topology

namespace KalaiVempala.Multiplicative.KVFresh

lemma positivepart_exp_half {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => max 0 (x-a) * Real.exp (-(η*x))) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, max 0 (x-a) * Real.exp (-(η*x))) =
      Real.exp (-(η*a)) / η^2 := by
  have heq : (fun x : ℝ => max 0 (x-a) * Real.exp (-(η*x))) =
      (Ioi a).indicator (fun x => (x-a) * Real.exp (-(η*x))) := by
    funext x
    by_cases hx : a < x
    · simp only [mem_Ioi, hx, indicator_of_mem, max_eq_right (by linarith : 0 ≤ x-a)]
    · rw [indicator_of_notMem (show x ∉ Ioi a from hx)]
      simp only [max_eq_left (by linarith : x-a ≤ 0), zero_mul]
  have ht := exponential_residual_tail hη a
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr ht.1
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hi.integrableOn
  · rw [heq, setIntegral_indicator measurableSet_Ioi]
    have hs : Ioi (0 : ℝ) ∩ Ioi a = Ioi a :=
      inter_eq_right.mpr (Ioi_subset_Ioi ha)
    rw [hs]
    exact ht.2

lemma laplace_residual_density {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => laplaceDensity η x * max 0 (|x|-a)) ∧
    (∫ x : ℝ, laplaceDensity η x * max 0 (|x|-a)) =
      Real.exp (-(η*a)) / η := by
  have ht := positivepart_exp_half hη ha
  have hi := (integrable_comp_abs_of_Ioi ht.1).const_mul (η/2)
  have heq : (fun x : ℝ => laplaceDensity η x * max 0 (|x|-a)) =
      (fun x : ℝ => (η/2) * (max 0 (|x|-a) * Real.exp (-(η*|x|)))) := by
    funext x
    unfold laplaceDensity
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hi
  · rw [heq, integral_const_mul,
      integral_comp_abs (f := fun x : ℝ => max 0 (x-a) * Real.exp (-(η*x))), ht.2]
    field_simp

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open MeasureTheory
open scoped BigOperators

theorem norm_le_residual_sum {n : ℕ} (p : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    ‖p‖ ≤ a + ∑ i, max 0 (|p i|-a) := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg ha (Finset.sum_nonneg fun i _ => le_max_left ..))).mpr
  intro i
  have hi : max 0 (|p i|-a) ≤ ∑ j, max 0 (|p j|-a) :=
    Finset.single_le_sum (f := fun j => max 0 (|p j|-a))
      (fun j _ => le_max_left ..) (Finset.mem_univ i)
  have hm := le_max_right (0 : ℝ) (|p i|-a)
  rw [Real.norm_eq_abs]
  linarith

theorem norm_integrable_of_residuals {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 ≤ a)
    (hi : ∀ i : Fin n, Integrable (fun p : Fin n → ℝ => max 0 (|p i|-a)) μ) :
    Integrable (fun p : Fin n → ℝ => ‖p‖) μ := by
  have hs : Integrable (fun p : Fin n → ℝ => a + ∑ i, max 0 (|p i|-a)) μ :=
    (integrable_const a).add (integrable_finsetSum _ fun i _ => hi i)
  apply hs.mono' continuous_norm.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [norm_norm] using norm_le_residual_sum p a ha

theorem expected_norm_le_residuals {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 ≤ a)
    (hi : ∀ i : Fin n, Integrable (fun p : Fin n → ℝ => max 0 (|p i|-a)) μ) :
    ∫ p, ‖p‖ ∂μ ≤ a + ∑ i, ∫ p, max 0 (|p i|-a) ∂μ := by
  have hs : Integrable (fun p : Fin n → ℝ => ∑ i, max 0 (|p i|-a)) μ :=
    integrable_finsetSum _ fun i _ => hi i
  calc
    ∫ p, ‖p‖ ∂μ ≤ ∫ p, a + ∑ i, max 0 (|p i|-a) ∂μ :=
      integral_mono (norm_integrable_of_residuals μ a ha hi)
        ((integrable_const a).add hs) (fun p => norm_le_residual_sum p a ha)
    _ = a + ∑ i, ∫ p, max 0 (|p i|-a) ∂μ := by
      rw [integral_add (integrable_const a) hs, integral_finsetSum _ (fun i _ => hi i)]
      simp

theorem expected_norm_of_residual_formula {n : ℕ} (hn : 1 ≤ n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η)
    (hi : ∀ (a : ℝ), 0 ≤ a → ∀ i : Fin n,
      Integrable (fun p : Fin n → ℝ => max 0 (|p i|-a)) μ)
    (he : ∀ (a : ℝ), 0 ≤ a → ∀ i : Fin n,
      (∫ p, max 0 (|p i|-a) ∂μ) = Real.exp (-η*a)/η) :
    ∫ p, ‖p‖ ∂μ ≤ (1+Real.log n)/η := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  let a : ℝ := Real.log n / η
  have ha : 0 ≤ a := div_nonneg hlog hη.le
  have hb := expected_norm_le_residuals μ a ha (hi a ha)
  simp_rw [he a ha] at hb
  have hexp : Real.exp (-η*a) = (n : ℝ)⁻¹ := by
    have hh : -η*a = -Real.log n := by dsimp [a]; field_simp
    rw [hh, Real.exp_neg, Real.exp_log hn0]
  rw [hexp] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hid : a + (n : ℝ) * ((n : ℝ)⁻¹ / η) = (1+Real.log n)/η := by
    dsimp [a]
    field_simp
    ring
  rwa [hid] at hb

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory

namespace KalaiVempala.Multiplicative.KVFresh

lemma native_residual_integrable {n : ℕ} {η : ℝ} (hη : 0 < η)
    {a : ℝ} (ha : 0 ≤ a) (i : Fin n) :
    Integrable (fun p : Fin n → ℝ => max 0 (|p i|-a)) (laplaceLaw n η) :=
  integrable_coordinate_laplace hη i _ (laplace_residual_density hη ha).1

lemma native_residual_integral {n : ℕ} {η : ℝ} (hη : 0 < η)
    {a : ℝ} (ha : 0 ≤ a) (i : Fin n) :
    (∫ p : Fin n → ℝ, max 0 (|p i|-a) ∂laplaceLaw n η) =
      Real.exp (-η*a)/η := by
  rw [integral_coordinate_laplace hη i (fun x : ℝ => max 0 (|x|-a))]
  simpa only [neg_mul] using (laplace_residual_density hη ha).2

lemma native_norm_integrable (n : ℕ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun p : Fin n → ℝ => ‖p‖) (laplaceLaw n η) := by
  let := laplaceLaw_probability n hη
  exact norm_integrable_of_residuals _ 0 le_rfl (native_residual_integrable hη le_rfl)

lemma native_expected_norm {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    (∫ p : Fin n → ℝ, ‖p‖ ∂laplaceLaw n η) ≤ (1+Real.log n)/η := by
  let := laplaceLaw_probability n hη
  exact expected_norm_of_residual_formula hn _ η hη
    (fun _ ha => native_residual_integrable hη ha)
    (fun _ ha => native_residual_integral hη ha)

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open MeasureTheory Matrix OracleRO.ApproxFPL
open scoped BigOperators

theorem integrated_shared_perturbation {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (hMmeas : Measurable M) (D : ℝ)
    (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hnorm : Integrable (fun p : Fin n → ℝ => ‖p‖) μ)
    (s : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ∫ p, s t ⬝ᵥ M (prefixSum s t+p) ∂μ ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T + D*(∫ p, ‖p‖ ∂μ) := by
  have hi (t : ℕ) := oracle_loss_integrable Dset M hM hMmeas D hD μ (prefixSum s t) (s t)
  have hsum : Integrable (fun p => ∑ t ∈ Finset.Icc 1 T,
      s t ⬝ᵥ M (prefixSum s t+p)) μ := integrable_finsetSum _ (fun t _ => hi t)
  have hr : Integrable (fun p : Fin n → ℝ => M (prefixSum s T) ⬝ᵥ prefixSum s T + D*‖p‖) μ :=
    (integrable_const _).add (hnorm.const_mul D)
  have hb := integral_mono hsum hr (fun p => by
    simpa only [dotProduct_comm] using shared_perturbation_bound Dset M hM D hD s T p)
  rw [integral_finsetSum _ (fun t _ => hi t), integral_add (integrable_const _) (hnorm.const_mul D),
    integral_const_mul] at hb
  simpa using hb

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open Matrix OracleRO.ApproxFPL
open scoped BigOperators

theorem native_opt_nonnegative {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S) :
    0 ≤ M (prefixSum s T) ⬝ᵥ prefixSum s T := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hDnn _ (hM _).1 i)
  change 0 ≤ (∑ t ∈ Finset.Icc 1 T, s t) i
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg (fun t ht => hSnn _ (hs t ht) i)

theorem zero_dimension_conclusion (Dset : Set (Fin 0 → ℝ))
    (M : (Fin 0 → ℝ) → Fin 0 → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (D : ℝ) (hD : ∀ x ∈ Dset, ∀ y ∈ Dset, ∑ i, |x i-y i| ≤ D)
    (s : ℕ → Fin 0 → ℝ) (T : ℕ) (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    fplStarExpectedCost M s (ε/(2*A)) T ≤
      (1+ε)*(M (prefixSum s T) ⬝ᵥ prefixSum s T) + 4*A*D*(1+Real.log 0)/ε := by
  have hD0 := diameter_nonnegative Dset M hM D hD
  simp only [fplStarExpectedCost, dotProduct, Finset.univ_eq_empty, Finset.sum_empty,
    MeasureTheory.integral_zero, Finset.sum_const_zero, mul_zero, Real.log_zero, add_zero]
  positivity

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh

theorem exp_le_one_add_twice (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1+2*x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx1) hx (by ring : (1-x)+x=1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  have he := Real.exp_one_lt_three
  nlinarith

theorem native_parameter_constants (ε A : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 0 < A) :
    0 < ε/(2*A) ∧ Real.exp ((ε/(2*A))*A) ≤ 1+ε := by
  constructor
  · positivity
  · have hh : (ε/(2*A))*A = ε/2 := by field_simp
    rw [hh]
    have h := exp_le_one_add_twice (ε/2) (by positivity) (by linarith)
    linarith

theorem final_cost_constant (ε A D L O C : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : 0 < A) (hD : 0 ≤ D) (hL : 0 ≤ L) (hO : 0 ≤ O)
    (hC : C ≤ Real.exp ((ε/(2*A))*A) * (O + D*L/(ε/(2*A)))) :
    C ≤ (1+ε)*O + 4*A*D*L/ε := by
  have hexp := (native_parameter_constants ε A hε hε1 hA).2
  have hden : 0 < ε/(2*A) := by positivity
  have hnonneg : 0 ≤ O + D*L/(ε/(2*A)) := by positivity
  have h1 := hC.trans (mul_le_mul_of_nonneg_right hexp hnonneg)
  have h2 : (1+ε)*(D*L) ≤ 2*(D*L) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hD hL)
  have hd : D*L/(ε/(2*A)) = (2*A/ε)*(D*L) := by field_simp
  rw [hd] at h1
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*A/ε)
  ring_nf at h1 h3 ⊢
  linarith

end KalaiVempala.Multiplicative.KVFresh
end


section

namespace KalaiVempala.Multiplicative.KVFresh
open MeasureTheory Matrix OracleRO.ApproxFPL
open scoped BigOperators

theorem native_multiplicative_conclusion {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → Fin n → ℝ) (hM : Additive.IsArgminOracle Dset M)
    (hMmeas : Measurable M) (D : ℝ)
    (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i-d' i| ≤ D)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hA0 : 0 < A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    fplStarExpectedCost M s (ε/(2*A)) T ≤
      (1+ε)*(M (prefixSum s T) ⬝ᵥ prefixSum s T) + 4*A*D*(1+Real.log n)/ε := by
  by_cases hn : n=0
  · subst n
    simpa only [Nat.cast_zero] using zero_dimension_conclusion Dset M hM D hD s T A ε hA0 hε0
  have hn1 : 1 ≤ n := by omega
  let η := ε/(2*A)
  have hη : 0 < η := (native_parameter_constants ε A hε0 hε1 hA0).1
  let := laplaceLaw_probability n hη
  have hD0 := diameter_nonnegative Dset M hM D hD
  have hL : 0 ≤ 1+Real.log n := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
    linarith
  have hO := native_opt_nonnegative Dset S M hM hDnn hSnn s T hs
  apply final_cost_constant ε A D (1+Real.log n) _ _ hε0 hε1 hA0 hD0 hL hO
  have hshift : fplStarExpectedCost M s η T ≤ Real.exp (η*A) *
      ∑ t ∈ Finset.Icc 1 T, ∫ p, s t ⬝ᵥ M (prefixSum s t+p) ∂laplaceLaw n η := by
    unfold fplStarExpectedCost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    exact native_period_shift Dset S M hM hMmeas D hD A hA hDnn hSnn s t
      (Finset.mem_Icc.mp ht).1 (hs t ht) hη
  have hb := integrated_shared_perturbation Dset M hM hMmeas D hD
    (laplaceLaw n η) (native_norm_integrable n hη) s T
  have he := native_expected_norm hn1 hη
  have hlook := hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left he hD0))
  have hout := hshift.trans (mul_le_mul_of_nonneg_left hlook (Real.exp_pos _).le)
  simpa only [η, mul_div_assoc] using hout

end KalaiVempala.Multiplicative.KVFresh
end


section

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem theorem_1_1_b {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hA0 : 0 < A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    fplStarExpectedCost M s (ε / (2 * A)) T ≤
      (1 + ε) * (M (prefixSum s T) ⬝ᵥ prefixSum s T) + 4 * A * Ddiam * (1 + Real.log n) / ε := by
  exact KVFresh.native_multiplicative_conclusion Dset S M hM hMmeas Ddiam hD A hA s T hs
    hDnn hSnn hA0 ε hε0 hε1

end KalaiVempala.Multiplicative
end


theorem solution {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hs : ∀ t ∈ Finset.Icc 1 T, s t ∈ S)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hA0 : 0 < A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    KalaiVempala.Multiplicative.fplStarExpectedCost M s (ε / (2 * A)) T ≤
      (1 + ε) * (M (OracleRO.ApproxFPL.prefixSum s T) ⬝ᵥ OracleRO.ApproxFPL.prefixSum s T) + 4 * A * Ddiam * (1 + Real.log n) / ε := by
  exact KalaiVempala.Multiplicative.theorem_1_1_b Dset S M hM hMmeas Ddiam hD A hA s T hs hDnn hSnn hA0 ε hε0 hε1
