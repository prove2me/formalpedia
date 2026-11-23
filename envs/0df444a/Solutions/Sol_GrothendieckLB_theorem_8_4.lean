-- Prove2me | solution 1 for GrothendieckLB.theorem_8_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:21:15.518913+00:00
-- url     : https://prove2.me/submissions/79a4f74a-a50d-48c9-8676-1272728bbb82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_GrothendieckLB_p3NormSq
import Definitions.Def_ABPOnline_cG
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
import Theorems.Thm_GrothendieckLB_eq_38
import Theorems.Thm_GrothendieckLB_theorem_8_3
import Theorems.Thm_GrothendieckLB_theorem_8_5

section

-- Gaussian projection, contraction, and integrability lemmas adapted from LG’s symmetric-scheme proof.
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

end KG

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

end KG

open Real MeasureTheory Filter ProbabilityTheory Finset

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

section scheme
variable {k : ℕ}

/-- First moments `E[h(X) X_i]`. -/
noncomputable def mom1 (h : (Fin k → ℝ) → ℝ) (i : Fin k) : ℝ := ∫ x, h x * x i * phiK k x

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

end scheme

end KG

open Real MeasureTheory Filter ProbabilityTheory Finset

set_option linter.unusedSectionVars false

namespace KG

variable {k : ℕ}

noncomputable def proj (v x : Fin k → ℝ) : ℝ := ∑ i, v i * x i

lemma measurable_proj (v : Fin k → ℝ) : Measurable (proj v) := by
  unfold proj; fun_prop

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

end KG

end

section

open Finset Equiv MulAction

namespace CubicChaos

noncomputable def counts {n d : ℕ} (v : Fin n → Fin d) (i : Fin d) : ℕ :=
  Fintype.card {a // v a = i}

def tupleEquiv (d : ℕ) : (Fin 3 → Fin d) ≃ Fin d × Fin d × Fin d where
  toFun p := (p 0, p 1, p 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv p := funext fun i => by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨i,j,l⟩; rfl

lemma sum_triples {d : ℕ} (B : Fin d → Fin d → Fin d → ℝ) :
    ∑ p : Fin 3 → Fin d, B (p 0) (p 1) (p 2) = ∑ i, ∑ j, ∑ l, B i j l := by
  let f := fun p : Fin d × Fin d × Fin d => B p.1 p.2.1 p.2.2
  have h := (tupleEquiv d).sum_comp f
  simpa [f, tupleEquiv, Fintype.sum_prod_type] using h

lemma counts_three {d : ℕ} (v : Fin 3 → Fin d) (i : Fin d) :
    counts v i = (if v 0 = i then 1 else 0) + (if v 1 = i then 1 else 0) +
      (if v 2 = i then 1 else 0) := by
  classical
  rw [counts, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]

end CubicChaos

end

section

open MeasureTheory ProbabilityTheory Real Filter Finset KG GrothendieckLB
open PrivateAgnosticHalfspace.Gaussian
open scoped RealInnerProductSpace

namespace CubicChaos

private noncomputable def rawH (n : ℕ) (s : ℝ) : ℝ :=
  ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval s

@[simp] private lemma raw0 (z : ℝ) : rawH 0 z = 1 := by
  simp [rawH, Polynomial.hermite]
@[simp] private lemma raw1 (z : ℝ) : rawH 1 z = z := by
  simp [rawH, Polynomial.hermite_one]
@[simp] private lemma raw2 (z : ℝ) : rawH 2 z = z ^ 2 - 1 := by
  norm_num [rawH, Polynomial.hermite, Polynomial.derivative_mul] <;> ring
@[simp] private lemma raw3 (z : ℝ) : rawH 3 z = z ^ 3 - 3 * z := by
  norm_num [rawH, Polynomial.hermite, Polynomial.derivative_mul] <;> ring

private lemma raw_triple {d : ℕ} (z : Fin d → ℝ) (i j l : Fin d) :
    (∏ m : Fin d, rawH ((if i = m then 1 else 0) + (if j = m then 1 else 0) +
      (if l = m then 1 else 0)) (z m)) = H3 z i j l := by
  classical
  rw [← Finset.prod_subset (Finset.subset_univ ({i,j,l} : Finset (Fin d))) (by
    intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [Ne.symm hm.1, Ne.symm hm.2.1, Ne.symm hm.2.2])]
  by_cases h : i = j
  · subst j
    by_cases h : i = l
    · subst l; simp [H3] <;> ring
    · simp [H3, h, Ne.symm h] <;> ring
  · by_cases hi : i = l
    · subst l; simp [H3, h, Ne.symm h] <;> ring
    · by_cases hj : j = l
      · subst l; simp [H3, h, Ne.symm h] <;> ring
      · simp [H3, h, hi, hj, Ne.symm h, Ne.symm hi, Ne.symm hj] <;> ring

noncomputable def factor {d : ℕ} (κ : Fin d → ℕ) :=
  ∏ m, Real.sqrt ((κ m).factorial : ℝ)

theorem tensor_basis {d : ℕ} (v : Fin 3 → Fin d) (z : Fin d → ℝ) :
    H3 z (v 0) (v 1) (v 2) = factor (counts v) * hermite d (counts v) (WithLp.toLp 2 z) := by
  have norm_id (n : ℕ) (s : ℝ) : Real.sqrt (n.factorial : ℝ) *
      AMPLowDeg.RankOne.hermNorm n s = rawH n s := by
    unfold AMPLowDeg.RankOne.hermNorm rawH
    have h : 0 < Real.sqrt (n.factorial : ℝ) := by positivity
    field_simp
  unfold factor hermite
  rw [← Finset.prod_mul_distrib]
  simp only [norm_id, counts_three]
  exact (raw_triple z (v 0) (v 1) (v 2)).symm

end CubicChaos

end

section

open GrothendieckLB CubicChaos KG MeasureTheory ProbabilityTheory Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian
open scoped RealInnerProductSpace

namespace FiberChaos

noncomputable abbrev G (d : ℕ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

lemma gauss_eq {d : ℕ} (F : (Fin d → ℝ) → ℝ) :
    gaussExp F = ∫ z, F z ∂(G d) := by
  change (∫ z, F z * phiK d z) = _
  simp_rw [mul_comm (F _) (phiK _ _)]
  exact integral_phiK d F

noncomputable def coordH {d : ℕ} (κ : Fin d → ℕ) (z : Fin d → ℝ) :=
  hermite d κ (WithLp.toLp 2 z)
noncomputable def coef {d : ℕ} (u : (Fin d → ℝ) → ℝ) (κ : Fin d → ℕ) :=
  gaussExp (fun z => u z * coordH κ z)

lemma coordH_meas {d : ℕ} (κ : Fin d → ℕ) : Measurable (coordH κ) := by
  unfold coordH hermite AMPLowDeg.RankOne.hermNorm
  fun_prop

lemma coordH_int {d : ℕ} (κ : Fin d → ℕ) : Integrable (coordH κ) (G d) := by
  letI : IsProbabilityMeasure (gaussian d) := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hp : MeasurePreserving (WithLp.toLp 2) (G d) (gaussian d) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact hp.integrable_comp_of_integrable (((lemma_B_8 d).2.1 κ).integrable (by norm_num))

end FiberChaos

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB KG FiberChaos Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian

namespace FiberChaos

lemma cons_preserving (n : ℕ) : MeasurePreserving
    (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2)
    ((gaussianReal 0 1).prod (G n)) (G (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).symm
  have he : (fun p : ℝ × (Fin n → ℝ) => e.symm p) = fun p => Fin.cons p.1 p.2 := by
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  rw [← he]
  exact hm

lemma integral_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hm : Measurable F)
    (hi : Integrable F (G (n+1))) :
    (∫ z, F z ∂(G (n+1))) = ∫ t, ∫ s, F (Fin.cons s t) ∂(gaussianReal 0 1) ∂(G n) := by
  let c : ℝ × (Fin n → ℝ) → (Fin (n+1) → ℝ) := fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2
  have hp := cons_preserving n
  have law : HasLaw c (G (n+1)) ((gaussianReal 0 1).prod (G n)) :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  exact (law.integral_comp hm.aestronglyMeasurable).symm.trans
    (integral_prod_symm (F ∘ c) (hp.integrable_comp_of_integrable hi))

lemma stdExp_eq (F : ℝ → ℝ) : stdExp F = ∫ s, F s ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  unfold stdExp
  simp only [smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)

lemma he_eq_normalized (j : Fin 4) (s : ℝ) : he j s = AMPLowDeg.RankOne.hermNorm j.val s := by
  fin_cases j <;> norm_num [he, AMPLowDeg.RankOne.hermNorm, Polynomial.hermite,
    Polynomial.derivative_mul, Nat.factorial] <;> ring

lemma he_meas (j : Fin 4) : Measurable (he j) := by
  simp_rw [funext (he_eq_normalized j)]
  unfold AMPLowDeg.RankOne.hermNorm; fun_prop

lemma he_int (j : Fin 4) : Integrable (he j) (gaussianReal 0 1) := by
  let μ := gaussianReal 0 1
  have T := (measurePreserving_funUnique μ (Fin 1)).symm.integrable_comp_of_integrable
    (coordH_int (d := 1) (fun _ => j.val))
  apply T.congr
  exact Eventually.of_forall fun s => by
    simpa [Function.comp_def, coordH, hermite, Fintype.prod_unique] using (he_eq_normalized j s).symm

lemma product_cons {n : ℕ} (j : Fin 4) (κ : Fin n → ℕ) (s : ℝ) (t : Fin n → ℝ) :
    coordH (Fin.cons j.val κ) (Fin.cons s t) = he j s * coordH κ t := by
  unfold coordH hermite
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, he_eq_normalized]

noncomputable def fiber {n : ℕ} (k : (Fin (n+1) → ℝ) → ℝ) (j : Fin 4) (t : Fin n → ℝ) :=
  ∫ s, k (Fin.cons s t) * he j s ∂(gaussianReal 0 1)

lemma measurable_fiber {n : ℕ} {k : (Fin (n+1) → ℝ) → ℝ} (hm : Measurable k) (j : Fin 4) :
    Measurable (fiber k j) := by
  have h : Measurable (fun p : ℝ × (Fin n → ℝ) => k (Fin.cons p.1 p.2) * he j p.1) :=
    (hm.comp (cons_preserving n).measurable).mul ((he_meas j).comp measurable_fst)
  exact (h.stronglyMeasurable.integral_prod_left' (μ := gaussianReal 0 1)).measurable

lemma fiber_bound {n : ℕ} {k : (Fin (n+1) → ℝ) → ℝ} (hm : Measurable k)
    (hb : ∀ z, |k z| ≤ 1) (j : Fin 4) (t : Fin n → ℝ) :
    |fiber k j t| ≤ ∫ s, |he j s| ∂(gaussianReal 0 1) := by
  have hst : Measurable (fun s => k (Fin.cons s t)) :=
    hm.comp ((cons_preserving n).measurable.comp (measurable_id.prodMk measurable_const))
  have hi := (he_int j).bdd_mul hst.aestronglyMeasurable
    (Eventually.of_forall fun s => hb (Fin.cons s t))
  calc _ ≤ ∫ s, ‖k (Fin.cons s t) * he j s‖ ∂(gaussianReal 0 1) := norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono hi.norm (he_int j).abs (fun s => by
      simp only [Real.norm_eq_abs, abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hb (Fin.cons s t)) (abs_nonneg (he j s)))

end FiberChaos

end

section

open MeasureTheory ProbabilityTheory Real Filter Finset GrothendieckLB KG FiberChaos CubicChaos
open scoped RealInnerProductSpace

namespace FiberChaos

abbrev Vect (d : ℕ) := EuclideanSpace ℝ (Fin d)
noncomputable def rot {d : ℕ} (A : Vect d ≃ₗᵢ[ℝ] Vect d) (x : Fin d → ℝ) : Fin d → ℝ :=
  WithLp.ofLp (A (WithLp.toLp 2 x))

lemma rot_preserving {d : ℕ} (A : Vect d ≃ₗᵢ[ℝ] Vect d) : MeasurePreserving (rot A) (G d) (G d) := by
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hp : MeasurePreserving e (G d) (stdGaussian (Vect d)) :=
    ⟨e.measurable, map_pi_eq_stdGaussian⟩
  have hA : MeasurePreserving A (stdGaussian (Vect d)) (stdGaussian (Vect d)) :=
    ⟨A.continuous.measurable, stdGaussian_map A⟩
  exact hp.symm.comp (hA.comp hp)

lemma rot_dot {d : ℕ} (A : Vect d ≃ₗᵢ[ℝ] Vect d) (x y : Fin d → ℝ) :
    (∑ i, rot A x i * rot A y i) = ∑ i, x i * y i := by
  simpa only [rot, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using
    A.inner_map_map (WithLp.toLp 2 x) (WithLp.toLp 2 y)

lemma aligned_rotation {n : ℕ} (v : Fin (n+1) → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    ∃ A : Vect (n+1) ≃ₗᵢ[ℝ] Vect (n+1), ∀ x, proj v (rot A x) = x 0 := by
  let e : Vect (n+1) := EuclideanSpace.single 0 (1 : ℝ)
  let w : Vect (n+1) := WithLp.toLp 2 v
  have he : ‖e‖ = 1 := by simp [e]
  have hw : ‖w‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simpa [w, Real.norm_eq_abs, sq_abs] using hv
  let A := (ℝ ∙ (e - w))ᗮ.reflection
  have ha : A e = w := Submodule.reflection_sub (he.trans hw.symm)
  refine ⟨A, fun x => ?_⟩
  have h := A.inner_map_map (WithLp.toLp 2 x) e
  rw [ha, show e = EuclideanSpace.single 0 (1 : ℝ) by rfl, EuclideanSpace.inner_single_right] at h
  simpa [proj, rot, w, PiLp.inner_apply] using h

noncomputable def tensorKernel {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l, H3 x i j l * H3 y i j l

lemma kernel_rot {d : ℕ} (A : Vect d ≃ₗᵢ[ℝ] Vect d) (x y : Fin d → ℝ) :
    tensorKernel (rot A x) (rot A y) = tensorKernel x y := by
  unfold tensorKernel
  rw [sum_H3_mul_H3, sum_H3_mul_H3, sum_add_distrib, sum_add_distrib]
  simp only [sq, rot_dot]

lemma measurable_kernel {d : ℕ} : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => tensorKernel p.1 p.2) := by
  unfold tensorKernel
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun l _ => ((measurable_H3 i j l).comp measurable_fst).mul
      ((measurable_H3 i j l).comp measurable_snd)

lemma hermite3_int {d : ℕ} (i j l : Fin d) : Integrable (fun z : Fin d → ℝ => H3 z i j l) (G d) := by
  let p : Fin 3 → Fin d := ![i,j,l]
  have h := (coordH_int (counts p)).const_mul (factor (counts p))
  refine h.congr (Eventually.of_forall fun z => ?_)
  exact (tensor_basis p z).symm

lemma kernel_norm {d : ℕ} {k : (Fin d → ℝ) → ℝ} (hm : Measurable k) (hb : ∀ z, |k z| ≤ 1) :
    p3NormSq k = 1 / 6 * ∫ x, ∫ y, k x * k y * tensorKernel x y ∂(G d) ∂(G d) := by
  classical
  let Q := fun (p : Fin 3 → Fin d) (z : Fin d → ℝ) => k z * H3 z (p 0) (p 1) (p 2)
  have hQ (p) : Integrable (Q p) (G d) :=
    (hermite3_int (p 0) (p 1) (p 2)).bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hb)
  have hcoef (p) : cubicMoment k (p 0) (p 1) (p 2) = ∫ z, Q p z ∂(G d) := gauss_eq _
  have expand (x y) : k x * k y * tensorKernel x y = ∑ p : Fin 3 → Fin d, Q p x * Q p y := by
    unfold tensorKernel
    rw [← sum_triples]
    simp only [Finset.mul_sum]
    apply sum_congr rfl
    intro p _
    dsimp [Q]; ring
  have innerEq (x) : (∫ y, k x * k y * tensorKernel x y ∂(G d)) =
      ∑ p : Fin 3 → Fin d, Q p x * ∫ y, Q p y ∂(G d) := by
    simp_rw [expand, integral_finsetSum _ fun p _ => (hQ p).const_mul (Q p x), integral_const_mul]
  unfold p3NormSq p3Inner
  congr 1
  rw [← sum_triples]
  simp_rw [innerEq, integral_finsetSum _ fun p _ => (hQ p).mul_const (∫ y, Q p y ∂(G d)),
    integral_mul_const, hcoef]

lemma rotation_invariant {d : ℕ} {k : (Fin d → ℝ) → ℝ} (hm : Measurable k) (hb : ∀ z, |k z| ≤ 1)
    (A : Vect d ≃ₗᵢ[ℝ] Vect d) : p3NormSq (k ∘ rot A) = p3NormSq k := by
  have hp := rot_preserving A
  have law : HasLaw (rot A) (G d) (G d) := ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  let F := fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 * k p.2 * tensorKernel p.1 p.2
  have hF : Measurable F := (((hm.comp measurable_fst).mul (hm.comp measurable_snd))).mul measurable_kernel
  have hinner (x : Fin d → ℝ) :
      (∫ y, k (rot A x) * k (rot A y) * tensorKernel x y ∂(G d)) =
      ∫ y, F (rot A x, y) ∂(G d) := by
    calc _ = ∫ y, F (rot A x, rot A y) ∂(G d) := by simp [F, kernel_rot]
      _ = _ := law.integral_comp ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  rw [kernel_norm (hm.comp hp.measurable) (fun z => hb _), kernel_norm hm hb]
  simp only [Function.comp_apply, hinner]
  congr 1
  exact law.integral_comp (hF.stronglyMeasurable.integral_prod_right' (ν := G d)).aestronglyMeasurable

end FiberChaos

end

section

open MeasureTheory ProbabilityTheory Real Filter Finset GrothendieckLB KG

namespace DisagreementBounds

noncomputable abbrev prodGauss (d : ℕ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

lemma gaussExp_eq {d : ℕ} (F : (Fin d → ℝ) → ℝ) :
    gaussExp F = ∫ z, F z ∂(prodGauss d) := by
  change (∫ z, F z * phiK d z) = _
  simp_rw [mul_comm (F _) (phiK _ _)]
  exact integral_phiK d F

lemma aligned_direction {d : ℕ} (h : (Fin d → ℝ) → ℝ) (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1) (hα : 0 < p1Norm h) :
    ∃ v : Fin d → ℝ, (∑ i, v i ^ 2 = 1) ∧
      (∫ z, h z * proj v z ∂(prodGauss d)) = p1Norm h := by
  let α := p1Norm h
  have hαsq : α ^ 2 = ∑ i, mom1 h i * mom1 h i :=
    Real.sq_sqrt (sum_nonneg fun i _ => mul_self_nonneg _)
  let v : Fin d → ℝ := fun i => mom1 h i / α
  have hv : ∑ i, v i ^ 2 = 1 := by
    simp only [v, div_pow, ← sum_div]
    rw [div_eq_one_iff_eq (pow_ne_zero _ hα.ne'), hαsq]
    exact sum_congr rfl fun i _ => sq _
  have hva : ∑ i, v i * mom1 h i = α := by
    simp only [v, div_mul_eq_mul_div, ← sum_div]
    rw [← hαsq]; field_simp
  refine ⟨v, hv, ?_⟩
  change _ = α
  rw [← hva, sum_mom1_eq h hm hb, ← gaussExp_eq]
  simp only [pow_one]
  rfl

lemma sign_budget {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g)
    (v : Fin d → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    (∫ z, |proj v z| * disagreePart f g z ^ 2 ∂(prodGauss d)) +
      (∫ z, agreePart f g z * proj v z ∂(prodGauss d)) ≤ ABPOnline.cG := by
  let μ := prodGauss d
  let S := proj v
  let h := agreePart f g
  let w := fun z => disagreePart f g z ^ 2
  have hS : Measurable S := measurable_proj v
  have hlaw : HasLaw S (gaussianReal 0 1) μ := ⟨hS.aemeasurable, proj_law d v hv⟩
  have hm : Measurable h := (hf.1.add hg.1).div_const 2
  have wm : Measurable w := ((hf.1.sub hg.1).div_const 2).pow_const _
  have hsign (z) : |h z| + w z = 1 ∧ |h z| ≤ 1 ∧ 0 ≤ w z ∧ w z ≤ 1 := by
    rcases hf.2 z with hf' | hf' <;> rcases hg.2 z with hg' | hg' <;>
      norm_num [h, w, agreePart, disagreePart, hf', hg']
  have hSi : Integrable S μ := (hlaw.measurePreserving hS).integrable_comp_of_integrable
    (IsGaussian.integrable_id : Integrable id (gaussianReal 0 1))
  have hWS := hSi.abs.mul_bdd wm.aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hsign z).2.2.1]
      using (hsign z).2.2.2)
  have hHS := hSi.bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall fun z => (hsign z).2.1)
  change (∫ z, |S z| * w z ∂μ) + (∫ z, h z * S z ∂μ) ≤ _
  rw [← integral_add hWS hHS]
  calc _ ≤ ∫ z, |S z| ∂μ := by
              apply integral_mono (hWS.add hHS) hSi.abs
              intro z
              have hm' := le_abs_self (h z * S z)
              rw [abs_mul] at hm'
              have h' := congrArg (fun t => t * |S z|) (hsign z).1
              change |S z| * w z + h z * S z ≤ |S z|
              nlinarith only [hm', h']
    _ = ABPOnline.cG := (hlaw.integral_comp measurable_abs.aestronglyMeasurable).trans gauss_abs_one

end DisagreementBounds

end

section

open GrothendieckLB KG FiberChaos MeasureTheory ProbabilityTheory Real Finset Filter
open DisagreementBounds

private lemma ternary_abs {α : Type*} [MeasurableSpace α] {k : α → ℝ} (hk : IsTernaryFn k) (z) :
    |k z| ≤ 1 ∧ k z ^ 2 ≤ 1 := by
  rcases hk.2 z with h | h | h <;> norm_num [h]

private theorem fiber_jensen {n : ℕ} {K : (Fin (n+1) → ℝ) → ℝ} (hK : IsTernaryFn K) :
    let β := fun t : Fin n → ℝ => GrothendieckLB.beta (fun s => K (Fin.cons s t))
    let b := ∫ t, β t ∂(G n)
    (∫ t, V (fun s => K (Fin.cons s t)) ∂(G n)) ≤ 3 * ABPOnline.cG * b - b ^ 2 := by
  intro β b
  let ν := ABPOnline.cG
  have hKm := hK.1.comp (cons_preserving n).measurable
  have hβm : Measurable β := by
    have hf : Measurable (fun p : ℝ × (Fin n → ℝ) => |p.1| * K (Fin.cons p.1 p.2) ^ 2) :=
      (measurable_abs.comp measurable_fst).mul (hKm.pow_const 2)
    have hi := hf.stronglyMeasurable.integral_prod_left' (μ := gaussianReal 0 1)
    simpa [β, GrothendieckLB.beta, stdExp_eq] using hi.measurable
  have hβ (t : Fin n → ℝ) : 0 ≤ β t ∧ β t ≤ ν := by
    have hs : Measurable (fun s => K (Fin.cons s t)) := hKm.comp (measurable_id.prodMk measurable_const)
    have hlt : Integrable (fun s : ℝ => |s|) (gaussianReal 0 1) := IsGaussian.integrable_id.abs
    have hb := fun s => (ternary_abs hK (Fin.cons s t)).2
    have hint := hlt.mul_bdd (hs.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (K (Fin.cons s t)))] using hb s)
    change 0 ≤ stdExp _ ∧ stdExp _ ≤ _
    rw [stdExp_eq]
    refine ⟨integral_nonneg fun s => mul_nonneg (abs_nonneg _) (sq_nonneg _), ?_⟩
    exact (integral_mono hint hlt (fun s => by
      simpa using mul_le_mul_of_nonneg_left (hb s) (abs_nonneg s))).trans_eq gauss_abs_one
  have hβLp : MemLp β 2 (G n) := MemLp.of_bound hβm.aestronglyMeasurable ν
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hβ t).1]; exact (hβ t).2)
  have hiβ := hβLp.integrable (by norm_num)
  have hVs : Integrable (fun t => V (fun s => K (Fin.cons s t))) (G n) := by
    have hm (j : Fin 4) : MemLp (fiber K j) 2 (G n) :=
      MemLp.of_bound (measurable_fiber hK.1 j).aestronglyMeasurable _
        (Eventually.of_forall fun t => fiber_bound hK.1 (fun z => (ternary_abs hK z).1) j t)
    have hs := integrable_finsetSum (μ := G n) (s := univ) (fun j _ => (hm j).integrable_sq)
    simpa only [V, stdExp_eq, fiber] using hs
  have hp (t : Fin n → ℝ) : V (fun s => K (Fin.cons s t)) ≤ 3 * ν * β t - β t ^ 2 := by
    apply theorem_8_3
    exact ⟨hKm.comp (measurable_id.prodMk measurable_const), fun s => hK.2 _⟩
  have hbnd := integral_mono hVs ((hiβ.const_mul (3*ν)).sub hβLp.integrable_sq) hp
  simp only [Pi.sub_apply] at hbnd
  rw [integral_sub (hiβ.const_mul (3*ν)) hβLp.integrable_sq, integral_const_mul] at hbnd
  have hvar := variance_nonneg β (G n)
  rw [variance_eq_sub hβLp] at hvar
  change 0 ≤ (∫ t, β t ^ 2 ∂(G n)) - b ^ 2 at hvar
  change _ ≤ 3 * ν * b - _ at hbnd ⊢
  linarith only [hvar, hbnd]

private lemma budget_rot {n : ℕ} {k : (Fin (n+1) → ℝ) → ℝ} (hk : IsTernaryFn k)
    (v : Fin (n+1) → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    (A : Vect (n+1) ≃ₗᵢ[ℝ] Vect (n+1)) (hA : ∀ z, proj v (rot A z) = z 0) :
    (∫ t : Fin n → ℝ, GrothendieckLB.beta (fun s => k (rot A (Fin.cons s t))) ∂(G n)) =
    ∫ z, |proj v z| * k z ^ 2 ∂(G (n+1)) := by
  let F := fun z => |proj v z| * k z ^ 2
  have hm : Measurable F := (measurable_proj v).abs.mul (hk.1.pow_const 2)
  have hS : HasLaw (proj v) (gaussianReal 0 1) (G (n+1)) :=
    ⟨(measurable_proj v).aemeasurable, proj_law _ _ hv⟩
  have hsi : Integrable (fun z => |proj v z|) (G (n+1)) :=
    (hS.measurePreserving (measurable_proj v)).integrable_comp_of_integrable
      (show Integrable (fun s : ℝ => |s|) (gaussianReal 0 1) from IsGaussian.integrable_id.abs)
  have hi : Integrable F (G (n+1)) := hsi.mul_bdd (hk.1.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k z))]
      using (ternary_abs hk z).2)
  have hp := rot_preserving A
  have hlaw : HasLaw (rot A) (G (n+1)) (G (n+1)) := ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  refine Eq.trans ?_ (hlaw.integral_comp hm.aestronglyMeasurable)
  rw [integral_cons (hm.comp hp.measurable) (hp.integrable_comp_of_integrable hi)]
  simp only [Function.comp_apply, F, hA, Fin.cons_zero, GrothendieckLB.beta, stdExp_eq]

theorem solution {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    p3NormSq (disagreePart f g) ≤
      ABPOnline.cG ^ 2 * (3 * (1 - p1Norm (agreePart f g) / ABPOnline.cG) -
        (1 - p1Norm (agreePart f g) / ABPOnline.cG) ^ 2) := by
  let h := agreePart f g
  let k := disagreePart f g
  let ν := ABPOnline.cG
  let α := p1Norm h
  have hν : 0 < ν := Real.sqrt_pos.mpr (by positivity)
  change p3NormSq k ≤ ν ^ 2 * (3 * (1 - α / ν) - (1 - α / ν) ^ 2)
  by_cases hz : α = 0
  · have hs := theorem_8_5 hf hg
    change p3NormSq k ≤ Pfun (α / ν) at hs
    rw [hz, zero_div, Pfun, if_pos rfl] at hs
    apply hs.trans
    rw [hz, zero_div]
    norm_num
    have hsq : ν ^ 2 = 2 / π := Real.sq_sqrt (by positivity)
    rw [hsq]
    have hh := Real.pi_lt_four
    have hπ := Real.pi_pos
    field_simp
    linarith
  · have hα : 0 < α := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    cases d with
    | zero =>
      have hx : p1Norm h = 0 := by simp [p1Norm, p1Inner]
      exact False.elim (hz hx)
    | succ n =>
      have hh : Measurable h := (hf.1.add hg.1).div_const 2
      have hhb (z) : |h z| ≤ 1 := by
        rcases hf.2 z with h1 | h1 <;> rcases hg.2 z with h2 | h2 <;>
          norm_num [h, agreePart, h1, h2]
      have hk : IsTernaryFn k := by
        refine ⟨(hf.1.sub hg.1).div_const 2, fun z => ?_⟩
        rcases hf.2 z with h1 | h1 <;> rcases hg.2 z with h2 | h2 <;>
          norm_num [k, disagreePart, h1, h2]
      obtain ⟨v, hv, ha⟩ := aligned_direction h hh hhb hα
      obtain ⟨A, hA⟩ := aligned_rotation v hv
      let K := k ∘ rot A
      have hK : IsTernaryFn K := ⟨hk.1.comp (rot_preserving A).measurable, fun z => hk.2 _⟩
      let b := ∫ t : Fin n → ℝ, GrothendieckLB.beta (fun s => K (Fin.cons s t)) ∂(G n)
      have hupper := sign_budget hf hg v hv
      change (∫ z, |proj v z| * k z ^ 2 ∂(G (n+1))) + (∫ z, h z * proj v z ∂(G (n+1))) ≤ ν at hupper
      rw [← budget_rot hk v hv A hA, ha] at hupper
      change b + α ≤ ν at hupper
      have ha' := rotation_invariant hk.1 (fun z => (ternary_abs hk z).1) A
      have hred := eq_38 hK
      rw [gauss_eq] at hred
      have hJ := fiber_jensen hK
      change _ ≤ 3 * ν * b - b ^ 2 at hJ
      apply (ha'.symm.le.trans (hred.trans hJ)).trans
      have hrest : 0 ≤ (ν - α - b) * (3 * ν - (ν - α) - b) :=
        mul_nonneg (by linarith only [hupper]) (by linarith only [hupper, hν, hα])
      have hid : ν ^ 2 * (3 * (1 - α / ν) - (1 - α / ν) ^ 2) =
          3 * ν * (ν - α) - (ν - α) ^ 2 := by field_simp <;> ring
      rw [hid]
      nlinarith only [hrest]

end
