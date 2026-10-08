-- Prove2me | solution 1 for GrothendieckConstant.krivine_scheme_affine_constraint_of_f_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:26:44.467998+00:00
-- url     : https://prove2.me/submissions/a3a407ab-cc5f-49a0-9b83-93f60486d8d7

import Mathlib
import Definitions.Def_KrivineSchemeDefs
import Theorems.Thm_GrothendieckConstant_coeff_hermite_moments

/-!
# Gaussian moments on `Fin k → ℝ` (module 1 of the Grothendieck lane)
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace KG

/-- Standard Gaussian density on `Fin k → ℝ`. -/
noncomputable def phiK (k : ℕ) (x : Fin k → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma phiK_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ phiK k x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma measurable_phiK (k : ℕ) : Measurable (phiK k) := by
  unfold phiK
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

lemma pi_gauss (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal (phiK k x)) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : Fin k → ℝ, (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (phiK k x)) x
      = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      unfold phiK
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  have hint : Integrable (fun x : Fin k → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun i =>
      (integrable_gaussianPDFReal 0 1).indicator (hs i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_indicator (hs i), gaussianReal_apply 0 one_ne_zero (s i)]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
    (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)]
  rfl

/-- Integrals against the Gaussian density equal integrals against the product measure. -/
lemma integral_phiK (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    ∫ x, phiK k x * F x = ∫ x, F x ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  rw [pi_gauss, integral_withDensity_eq_integral_toReal_smul (measurable_phiK k).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (phiK_nonneg k x)]

end KG

namespace KG

open scoped RealInnerProductSpace

/-- One-dimensional absolute moments of the standard Gaussian. -/
lemma gauss_abs_moment (q : ℝ) (hq : -1 < q) :
    ∫ t, |t| ^ q ∂(gaussianReal 0 1) =
      2 * ((1 / Real.sqrt (2 * π)) * ((1 / 2 : ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Gamma ((q + 1) / 2))) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t • |t| ^ q =
      (fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ)))) |t| := by
    intro t
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.rpow_two, sq_abs]
    ring_nf
  simp_rw [h1]
  rw [integral_comp_abs (f := fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ))))]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)]

lemma gauss_abs_one : ∫ t, |t| ∂(gaussianReal 0 1) = Real.sqrt (2 / π) := by
  have h := gauss_abs_moment 1 (by norm_num)
  simp only [Real.rpow_one] at h
  rw [h]
  norm_num [Real.Gamma_one]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt π ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [hs]

lemma gauss_abs_three : ∫ t, |t| ^ 3 ∂(gaussianReal 0 1) = 2 * Real.sqrt (2 / π) := by
  have h := gauss_abs_moment 3 (by norm_num)
  have e : ∀ t : ℝ, |t| ^ (3 : ℝ) = |t| ^ (3 : ℕ) := fun t => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [e] at h
  rw [h]
  norm_num
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt π ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [hs]

/-- Projection law: for a unit vector `v`, `x ↦ ∑ v i * x i` is standard normal under the product measure. -/
lemma proj_law (k : ℕ) (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, v i * x i) = gaussianReal 0 1 := by
  set u : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 v
  have hu : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simpa [u, Real.norm_eq_abs, sq_abs] using hv
  have hfun : (fun x : Fin k → ℝ => ∑ i, v i * x i) = (fun y : EuclideanSpace ℝ (Fin k) => ⟪y, u⟫) ∘ (WithLp.toLp 2) := by
    funext x
    simp [u, PiLp.inner_apply]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian]
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)) := innerSL ℝ u
  have hL : ‖L‖ = 1 := by simp [L, hu]
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin k))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL]
    norm_num
  convert hm using 1
  congr 1
  ext y
  simpa [L] using (real_inner_comm u y)

/-- Absolute moments of a unit projection against the Gaussian density. -/
lemma proj_abs_moment (k : ℕ) (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) (n : ℕ) :
    ∫ x, phiK k x * |∑ i, v i * x i| ^ n = ∫ t, |t| ^ n ∂(gaussianReal 0 1) := by
  have hm : Measurable (fun x : Fin k → ℝ => ∑ i, v i * x i) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
  rw [integral_phiK]
  calc ∫ x, |∑ i, v i * x i| ^ n ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = ∫ t, |t| ^ n ∂((Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, v i * x i)) :=
        (integral_map hm.aemeasurable (continuous_abs.pow n).aestronglyMeasurable).symm
    _ = ∫ t, |t| ^ n ∂(gaussianReal 0 1) := by rw [proj_law k v hv]

end KG

/-! # An elementary polynomial-versus-exponential bound -/

namespace KG

/-- Polynomial times `exp (-A/4)` is dominated by a multiple of `exp (-A/8)`. -/
lemma poly_exp_le (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4))
      ≤ 2000 * ((1 + k) ^ 3 + 3072) * Real.exp (-(A / 8)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcube : (1 + A + k) ^ 3 ≤ 4 * ((1 + k) ^ 3 + A ^ 3) := by
    nlinarith [sq_nonneg (1 + k - A), mul_nonneg (add_nonneg zero_le_one hk) hA,
      mul_nonneg (mul_nonneg (add_nonneg zero_le_one hk) hA) (sq_nonneg (1 + k - A))]
  have hA3 : A ^ 3 ≤ 3072 * Real.exp (A / 8) := by
    have := Real.pow_div_factorial_le_exp (A / 8) (by positivity) 3
    norm_num [Nat.factorial] at this
    nlinarith
  have he1 : 1 ≤ Real.exp (A / 8) := Real.one_le_exp (by positivity)
  have hsplit : Real.exp (-(A / 4)) = (Real.exp (A / 8))⁻¹ * Real.exp (-(A / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-(A / 8)) := Real.exp_pos _
  have key : (1 + A + k) ^ 3 * (Real.exp (A / 8))⁻¹ ≤ 4 * ((1 + k) ^ 3 + 3072) := by
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    have : (0:ℝ) ≤ (1 + k) ^ 3 := by positivity
    nlinarith
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right key hpos.le
  nlinarith

end KG

/-!
# Third-order Hermite tensors (module 4a, pure algebra)
-/

namespace KG

open Finset

/-- `H3 x i j l = x_i x_j x_l - δ_ij x_l - δ_il x_j - δ_jl x_i`. -/
def H3 {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) : ℝ :=
  x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
    - (if j = l then x i else 0)

lemma sum_H3_mul_H3 {k : ℕ} (x y : Fin k → ℝ) :
    ∑ i, ∑ j, ∑ l, H3 x i j l * H3 y i j l
      = (∑ i, x i * y i) ^ 3
        - 3 * (∑ i, (x i ^ 2 + y i ^ 2)) * (∑ i, x i * y i)
        + (3 * k + 6) * (∑ i, x i * y i) := by
  simp only [H3, sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, sum_sub_distrib,
    sum_ite_eq, sum_ite_eq', mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true, sum_sub_distrib]
  set B := ∑ i, x i * y i
  set X := ∑ i, x i ^ 2
  set Y := ∑ i, y i ^ 2
  have s3 : ∑ a, ∑ b, ∑ c, x a * x b * x c * (y a * y b * y c) = B ^ 3 := by
    simp only [B, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring
  have two : ∀ F G : Fin k → ℝ, ∀ T : Fin k → Fin k → ℝ, (∀ a b, T a b = F a * G b) →
      ∑ a, ∑ b, T a b = (∑ a, F a) * ∑ b, G b := by
    intro F G T h
    simp only [h]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have p1 : ∑ a, ∑ b, x b * (y a * y a * y b) = Y * B :=
    two (fun a => y a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have p2 : ∑ a, ∑ b, x b * (y a * y b * y a) = Y * B :=
    two (fun a => y a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have p3 : ∑ a, ∑ b, x a * (y a * y b * y b) = B * Y :=
    two (fun a => x a * y a) (fun b => y b ^ 2) _ (fun a b => by ring)
  have q1 : ∑ a, ∑ b, x a * x a * x b * y b = X * B :=
    two (fun a => x a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have q2 : ∑ a, ∑ b, x a * x b * x a * y b = X * B :=
    two (fun a => x a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have q3 : ∑ a, ∑ b, x a * x b * x b * y a = B * X :=
    two (fun a => x a * y a) (fun b => x b ^ 2) _ (fun a b => by ring)
  have c1 : ∑ _a : Fin k, ∑ b, x b * y b = k * B := by
    simp [B]
  have c2 : ∑ a, ∑ _b : Fin k, x a * y a = k * B := by
    simp [B, Finset.mul_sum]
  have hXY : ∑ i, (x i ^ 2 + y i ^ 2) = X + Y := sum_add_distrib
  rw [s3, p1, p2, p3, q1, q2, q3, c1, c2, hXY]
  ring

lemma sum_H3_mul_cube {k : ℕ} (x v : Fin k → ℝ) :
    ∑ i, ∑ j, ∑ l, H3 x i j l * (v i * v j * v l)
      = (∑ i, v i * x i) ^ 3 - 3 * (∑ i, v i ^ 2) * (∑ i, v i * x i) := by
  have h := sum_H3_mul_H3 x v
  simp only [H3, sub_mul, ite_mul, zero_mul, sum_sub_distrib, sum_ite_eq, mem_univ, if_true,
    Finset.sum_ite_irrel, sum_const_zero]
  set s := ∑ i, v i * x i
  set V := ∑ i, v i ^ 2
  have two : ∀ F G : Fin k → ℝ, ∀ T : Fin k → Fin k → ℝ, (∀ a b, T a b = F a * G b) →
      ∑ a, ∑ b, T a b = (∑ a, F a) * ∑ b, G b := by
    intro F G T h
    simp only [h]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have s3 : ∑ a, ∑ b, ∑ c, x a * x b * x c * (v a * v b * v c) = s ^ 3 := by
    simp only [s, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring
  have p1 : ∑ a, ∑ b, x b * (v a * v a * v b) = V * s :=
    two (fun a => v a ^ 2) (fun b => v b * x b) _ (fun a b => by ring)
  have p2 : ∑ a, ∑ b, x b * (v a * v b * v a) = V * s :=
    two (fun a => v a ^ 2) (fun b => v b * x b) _ (fun a b => by ring)
  have p3 : ∑ a, ∑ b, x a * (v a * v b * v b) = s * V :=
    two (fun a => v a * x a) (fun b => v b ^ 2) _ (fun a b => by ring)
  rw [s3, p1, p2, p3]
  ring

/-- Cauchy–Schwarz for triple sums. -/
lemma sq_sum3_le {k : ℕ} (T W : Fin k → Fin k → Fin k → ℝ) :
    (∑ i, ∑ j, ∑ l, T i j l * W i j l) ^ 2
      ≤ (∑ i, ∑ j, ∑ l, T i j l ^ 2) * (∑ i, ∑ j, ∑ l, W i j l ^ 2) := by
  have e : ∀ F : Fin k → Fin k → Fin k → ℝ,
      ∑ i, ∑ j, ∑ l, F i j l = ∑ p : Fin k × Fin k × Fin k, F p.1 p.2.1 p.2.2 := by
    intro F
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  rw [e (fun i j l => T i j l * W i j l), e (fun i j l => T i j l ^ 2), e (fun i j l => W i j l ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma sum_cube_sq {k : ℕ} (v : Fin k → ℝ) :
    ∑ i, ∑ j, ∑ l, (v i * v j * v l) ^ 2 = (∑ i, v i ^ 2) ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  ring

end KG

/-!
# Hermite moments and their integrability (module 4b)
-/

open Real MeasureTheory Filter ProbabilityTheory GrothendieckConstant Finset

set_option linter.unusedSectionVars false

namespace KG

lemma gaussianPDFReal_std (s : ℝ) :
    gaussianPDFReal 0 1 s = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(s ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

lemma phiK_le_exp {k : ℕ} (x : Fin k → ℝ) : phiK k x ≤ Real.exp (-((∑ i, x i ^ 2) / 2)) := by
  unfold phiK
  rw [show -((∑ i, x i ^ 2) / 2) = ∑ i, -(x i ^ 2 / 2) by rw [sum_div, sum_neg_distrib],
    Real.exp_sum]
  refine prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) fun i _ => ?_
  rw [gaussianPDFReal_std]
  have : 1 ≤ Real.sqrt (2 * π) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x i ^ 2 / 2)) ≤ 1 * Real.exp (-(x i ^ 2 / 2)) := by
        gcongr; exact inv_le_one_of_one_le₀ this
    _ = _ := one_mul _

lemma integrable_exp_Q (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Fin k → ℝ => Real.exp (-(b * ∑ i, x i ^ 2))) := by
  have h1 : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (-b * x i ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ s => Real.exp (-b * s ^ 2))
      fun _ => integrable_exp_neg_mul_sq hb
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_sum, mul_sum, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

/-- A bounded function times a cubic-growth weight times the Gaussian density is integrable. -/
lemma integrable_poly_phi {k : ℕ} (h p : (Fin k → ℝ) → ℝ) (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) (hp : Measurable p) (C : ℝ) (hC : 0 ≤ C)
    (hpC : ∀ x, |p x| ≤ C * (1 + ∑ i, x i ^ 2) ^ 3) :
    Integrable (fun x => h x * p x * phiK k x) := by
  refine ((integrable_exp_Q k (1 / 4) (by norm_num)).const_mul (C * (2000 * 3073 / 500))).mono'
    ((hh.mul hp).mul (measurable_phiK k)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  set Q := ∑ i, x i ^ 2
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have hphi := phiK_le_exp x
  have hphi0 := phiK_nonneg k x
  have key := poly_exp_le 0 (A := 2 * Q) (by positivity)
  simp only [Nat.cast_zero, add_zero] at key
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hphi0]
  have h1 : (1 + Q) ^ 3 ≤ (1 + 2 * Q) ^ 3 := by gcongr; linarith
  have e1 : -(2 * Q / 4) = -(Q / 2) := by ring
  have e2 : -(2 * Q / 8) = -(1 / 4 * Q) := by ring
  rw [e1, e2] at key
  calc |h x| * |p x| * phiK k x ≤ 1 * (C * (1 + Q) ^ 3) * Real.exp (-(Q / 2)) := by
        gcongr
        · exact hb x
        · exact hpC x
    _ ≤ C * ((1 + 2 * Q) ^ 3 * Real.exp (-(Q / 2))) := by
        rw [one_mul, mul_assoc]; gcongr
    _ ≤ C * (2000 * (1 + 3072) / 500 * Real.exp (-(1 / 4 * Q))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        norm_num at key ⊢; linarith
    _ = _ := by norm_num; ring

lemma abs_coord_le {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 + ∑ j, x j ^ 2 := by
  have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + 1 / 2), sq_nonneg (x i - 1 / 2)]

lemma one_le_oneQ {k : ℕ} (x : Fin k → ℝ) : 1 ≤ 1 + ∑ j, x j ^ 2 := by
  have := sum_nonneg (s := univ) fun j _ => sq_nonneg (x j); linarith

lemma abs_coord_le3 {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  have h1 := one_le_oneQ x
  have := abs_coord_le x i
  nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 3 by norm_num), pow_one (1 + ∑ j, x j ^ 2)]

lemma abs_H3_le {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) :
    |H3 x i j l| ≤ 4 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  set M := 1 + ∑ j, x j ^ 2
  have h1 : 1 ≤ M := one_le_oneQ x
  have hi := abs_coord_le x i; have hj := abs_coord_le x j; have hl := abs_coord_le x l
  have hM3 : M ≤ M ^ 3 := by nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 3 by norm_num)]
  have hprod : |x i * x j * x l| ≤ M ^ 3 := by
    rw [abs_mul, abs_mul, pow_succ, pow_succ, pow_one]
    gcongr
  have hite : ∀ (P : Prop) [Decidable P] (z : ℝ), |z| ≤ M → |(if P then z else 0)| ≤ M ^ 3 := by
    intro P _ z hz
    split_ifs
    · exact hz.trans hM3
    · simp; positivity
  unfold H3
  calc _ ≤ |x i * x j * x l| + |(if i = j then x l else 0)| + |(if i = l then x j else 0)|
        + |(if j = l then x i else 0)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ M ^ 3 + M ^ 3 + M ^ 3 + M ^ 3 := by
        gcongr
        · exact hite _ _ hl
        · exact hite _ _ hj
        · exact hite _ _ hi
    _ = _ := by ring

section scheme
variable {k : ℕ}

/-- First moments `E[h(X) X_i]`. -/
noncomputable def mom1 (h : (Fin k → ℝ) → ℝ) (i : Fin k) : ℝ := ∫ x, h x * x i * phiK k x

/-- Third Hermite moments `E[h(X) H3(X)_{ijl}]`. -/
noncomputable def mom3 (h : (Fin k → ℝ) → ℝ) (i j l : Fin k) : ℝ :=
  ∫ x, h x * H3 x i j l * phiK k x

lemma measurable_H3 (i j l : Fin k) : Measurable fun x : Fin k → ℝ => H3 x i j l := by
  have hite : ∀ (P : Prop) [Decidable P] (m : Fin k),
      Measurable fun x : Fin k → ℝ => if P then x m else 0 := by
    intro P _ m
    by_cases hP : P <;> simp [hP]; fun_prop
  unfold H3
  exact ((((measurable_pi_apply i).mul (measurable_pi_apply j)).mul
    (measurable_pi_apply l)).sub (hite _ l)).sub (hite _ j) |>.sub (hite _ i)

lemma integrable_mom1 (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i : Fin k) : Integrable (fun x => h x * x i * phiK k x) :=
  integrable_poly_phi h (fun x => x i) hh hb (measurable_pi_apply i) 1 zero_le_one
    fun x => abs_coord_le3 x i

lemma integrable_mom3 (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i j l : Fin k) : Integrable (fun x => h x * H3 x i j l * phiK k x) :=
  integrable_poly_phi h (fun x => H3 x i j l) hh hb (measurable_H3 i j l) 4 (by norm_num)
    fun x => abs_H3_le x i j l

variable (S : KrivineScheme k)

lemma abs_f_le (x : Fin k → ℝ) : |S.f x| ≤ 1 := by
  rcases S.f_sign x with h | h <;> simp [h]

lemma abs_g_le (x : Fin k → ℝ) : |S.g x| ≤ 1 := by
  rcases S.g_sign x with h | h <;> simp [h]

end scheme

end KG

/-!
# The affine constraint for symmetric schemes (module 5)

For every measurable `h` with `|h| ≤ 1`, with `a = E[h X]` and `T = E[h H3(X)]`,
`π |a|² - 11/6 ≤ (π/12) |T|²`. Taking `h = f = g` gives `2 b₁ - 11/6 ≤ b₃`.
-/

open Real MeasureTheory Filter ProbabilityTheory GrothendieckConstant Finset

set_option linter.unusedSectionVars false

namespace KG

variable {k : ℕ}

noncomputable def proj (v x : Fin k → ℝ) : ℝ := ∑ i, v i * x i

lemma measurable_proj (v : Fin k → ℝ) : Measurable (proj v) := by
  unfold proj; fun_prop

lemma abs_proj_le (v x : Fin k → ℝ) :
    |proj v x| ≤ (∑ i, |v i|) * (1 + ∑ j, x j ^ 2) := by
  unfold proj
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_coord_le x i) (abs_nonneg _)

lemma abs_proj_pow_le (v x : Fin k → ℝ) (n : ℕ) (hn : n ≤ 3) :
    |proj v x ^ n| ≤ (1 + ∑ i, |v i|) ^ 3 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  have h1 := one_le_oneQ x
  have hv : 0 ≤ ∑ i, |v i| := sum_nonneg fun i _ => abs_nonneg _
  have hp : |proj v x| ≤ (1 + ∑ i, |v i|) * (1 + ∑ j, x j ^ 2) :=
    (abs_proj_le v x).trans (by gcongr; linarith)
  have hge : 1 ≤ (1 + ∑ i, |v i|) * (1 + ∑ j, x j ^ 2) := by nlinarith
  rw [abs_pow, ← mul_pow]
  calc |proj v x| ^ n ≤ ((1 + ∑ i, |v i|) * (1 + ∑ j, x j ^ 2)) ^ n := by gcongr
    _ ≤ _ := pow_le_pow_right₀ hge hn

lemma integrable_proj_pow (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) (n : ℕ) (hn : n ≤ 3) :
    Integrable (fun x => h x * proj v x ^ n * phiK k x) :=
  integrable_poly_phi h _ hh hb ((measurable_proj v).pow_const n) _ (by positivity)
    fun x => abs_proj_pow_le v x n hn

lemma integrable_abs_proj_pow (v : Fin k → ℝ) (n : ℕ) (hn : n ≤ 3) :
    Integrable (fun x => phiK k x * |proj v x| ^ n) := by
  have := integrable_poly_phi (fun _ => (1 : ℝ)) (fun x => |proj v x| ^ n) measurable_const
    (fun _ => by simp) ((measurable_proj v).abs.pow_const n) ((1 + ∑ i, |v i|) ^ 3) (by positivity)
    fun x => by rw [abs_pow, abs_abs, ← abs_pow]; exact abs_proj_pow_le v x n hn
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only; ring

lemma moment_le_abs (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) (n : ℕ) (hn : n ≤ 3) :
    ∫ x, h x * proj v x ^ n * phiK k x ≤ ∫ t, |t| ^ n ∂(gaussianReal 0 1) := by
  rw [← proj_abs_moment k v hv n]
  refine integral_mono (integrable_proj_pow h hh hb v n hn) (integrable_abs_proj_pow v n hn)
    fun x => ?_
  have h0 := phiK_nonneg k x
  have : h x * proj v x ^ n ≤ |proj v x| ^ n := by
    calc h x * proj v x ^ n ≤ |h x * proj v x ^ n| := le_abs_self _
      _ = |h x| * |proj v x| ^ n := by rw [abs_mul, abs_pow]
      _ ≤ 1 * |proj v x| ^ n := by gcongr; exact hb x
      _ = _ := one_mul _
  show h x * proj v x ^ n * phiK k x ≤ phiK k x * |proj v x| ^ n
  nlinarith

lemma sum_mom1_eq (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) :
    ∑ i, v i * mom1 h i = ∫ x, h x * proj v x ^ 1 * phiK k x := by
  unfold mom1
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (integrable_mom1 h hh hb i).const_mul (v i)]
  congr 1; ext x
  simp only [proj, pow_one, mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  ring

lemma sum_mom3_eq (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    ∑ i, ∑ j, ∑ l, mom3 h i j l * (v i * v j * v l)
      = (∫ x, h x * proj v x ^ 3 * phiK k x) - 3 * ∫ x, h x * proj v x ^ 1 * phiK k x := by
  have hint : ∀ i j l, Integrable fun x => (v i * v j * v l) * (h x * H3 x i j l * phiK k x) :=
    fun i j l => (integrable_mom3 h hh hb i j l).const_mul _
  have e1 : ∑ i, ∑ j, ∑ l, mom3 h i j l * (v i * v j * v l)
      = ∫ x, ∑ i, ∑ j, ∑ l, (v i * v j * v l) * (h x * H3 x i j l * phiK k x) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun l _ => hint i j l]
    refine sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint i j l]
    refine sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => hint i j l]
    refine sum_congr rfl fun l _ => ?_
    unfold mom3
    rw [integral_const_mul, mul_comm]
  have hpt : ∀ x, ∑ i, ∑ j, ∑ l, (v i * v j * v l) * (h x * H3 x i j l * phiK k x)
      = h x * proj v x ^ 3 * phiK k x - 3 * (h x * proj v x ^ 1 * phiK k x) := by
    intro x
    have hc := sum_H3_mul_cube x v
    rw [hv] at hc
    have e2 : ∑ i, ∑ j, ∑ l, (v i * v j * v l) * (h x * H3 x i j l * phiK k x)
        = h x * phiK k x * ∑ i, ∑ j, ∑ l, H3 x i j l * (v i * v j * v l) := by
      simp only [mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
      ring
    rw [e2, hc]
    unfold proj
    ring
  rw [e1, integral_congr_ae (Eventually.of_forall hpt),
    integral_sub (integrable_proj_pow h hh hb v 3 (by norm_num))
      ((integrable_proj_pow h hh hb v 1 (by norm_num)).const_mul 3), integral_const_mul]

/-- The final real-number step of the symmetric argument. -/
lemma sym_arith (α c N s0 : ℝ) (hs0 : 0 < s0) (hπ : π * s0 ^ 2 = 2) (hα0 : 0 ≤ α)
    (hαs : α ≤ s0) (hc : c ≤ 2 * s0 - 3 * α) (hN : c ^ 2 ≤ N) :
    π * α ^ 2 - 11 / 6 ≤ π / 12 * N := by
  have hpi := Real.pi_pos
  have hN0 : 0 ≤ N := (sq_nonneg c).trans hN
  rcases le_or_gt (3 * α) (2 * s0) with h | h
  · -- `π α² ≤ (4/9) π s0² = 8/9 < 11/6`
    have : π * α ^ 2 ≤ π * (4 / 9 * s0 ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hpi.le
      nlinarith
    have : 0 ≤ π / 12 * N := by positivity
    nlinarith
  · have hneg : c < 0 := by linarith
    have hsq : (3 * α - 2 * s0) ^ 2 ≤ c ^ 2 := by nlinarith
    have hkey : 3 * (α - s0) * (α + 5 * s0) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg <;> nlinarith
    have : π / 12 * (3 * α - 2 * s0) ^ 2 ≤ π / 12 * N :=
      mul_le_mul_of_nonneg_left (hsq.trans hN) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hkey hpi.le]

/-- **Symmetric affine constraint.** For any measurable `h` with `|h| ≤ 1`,
`π |E[h X]|² - 11/6 ≤ (π/12) |E[h H3(X)]|²`. -/
theorem sym_ineq (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1) :
    π * ∑ i, mom1 h i * mom1 h i - 11 / 6
      ≤ π / 12 * ∑ i, ∑ j, ∑ l, mom3 h i j l * mom3 h i j l := by
  set N1 := ∑ i, mom1 h i * mom1 h i with hN1
  set N3 := ∑ i, ∑ j, ∑ l, mom3 h i j l * mom3 h i j l
  have hpi := Real.pi_pos
  have hN3 : 0 ≤ N3 := sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun l _ =>
    mul_self_nonneg _
  set s0 := Real.sqrt (2 / π)
  have hs0 : 0 < s0 := Real.sqrt_pos.mpr (by positivity)
  have hπ : π * s0 ^ 2 = 2 := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have hN1nn : 0 ≤ N1 := sum_nonneg fun i _ => mul_self_nonneg (mom1 h i)
  rcases eq_or_lt_of_le hN1nn with h0 | h0
  · rw [← h0]; nlinarith [mul_nonneg hpi.le hN3]
  set α := Real.sqrt N1
  have hα : 0 < α := Real.sqrt_pos.mpr h0
  have hαsq : α ^ 2 = N1 := Real.sq_sqrt h0.le
  set v : Fin k → ℝ := fun i => mom1 h i / α
  have hv : ∑ i, v i ^ 2 = 1 := by
    simp only [v, div_pow, ← sum_div, hαsq]
    rw [div_eq_one_iff_eq h0.ne']
    exact sum_congr rfl fun i _ => sq _
  have hva : ∑ i, v i * mom1 h i = α := by
    simp only [v, div_mul_eq_mul_div, ← sum_div]
    rw [← hN1, ← hαsq]; field_simp
  -- `α = E[h s] ≤ E|s| = s0`
  have hαs : α ≤ s0 := by
    rw [← hva, sum_mom1_eq h hh hb v]
    have h1 := moment_le_abs h hh hb v hv 1 (by norm_num)
    simp only [pow_one] at h1 ⊢
    rwa [gauss_abs_one] at h1
  -- `c = E[h (s³ - 3s)] ≤ 2 s0 - 3α`
  set c := ∑ i, ∑ j, ∑ l, mom3 h i j l * (v i * v j * v l)
  have hc : c ≤ 2 * s0 - 3 * α := by
    have e := sum_mom3_eq h hh hb v hv
    rw [← sum_mom1_eq h hh hb v, hva] at e
    have h3 := moment_le_abs h hh hb v hv 3 (by norm_num)
    rw [gauss_abs_three] at h3
    change _ ≤ 2 * s0 at h3
    change c = _ at e
    linarith
  have hcs : c ^ 2 ≤ N3 := by
    have := sq_sum3_le (mom3 h) (fun i j l => v i * v j * v l)
    rw [sum_cube_sq, hv, one_pow, mul_one] at this
    simpa [N3, sq] using this
  have := sym_arith α c N3 s0 hs0 hπ hα.le hαs hc hcs
  rwa [hαsq] at this

end KG

open MeasureTheory ProbabilityTheory Real GrothendieckConstant

theorem solution (k : ℕ) (S : KrivineScheme k) (hfg : S.f = S.g) :
    2 * coeffLinear S - 11 / 6 ≤ coeffCubic S := by
  obtain ⟨h1, h3⟩ := GrothendieckConstant.coeff_hermite_moments k S
  have hs := KG.sym_ineq S.f S.measurable_f (KG.abs_f_le S)
  rw [h1, h3, ← hfg]
  show 2 * ((π / 2) * ∑ i, KG.mom1 S.f i * KG.mom1 S.f i) - 11 / 6
    ≤ (π / 12) * ∑ i, ∑ j, ∑ l, KG.mom3 S.f i j l * KG.mom3 S.f i j l
  linarith
