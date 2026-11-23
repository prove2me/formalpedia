-- Prove2me | solution 1 for GrothendieckLB.agreement_disagreement_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T14:47:37.160664+00:00
-- url     : https://prove2.me/submissions/0d4b0af5-dab4-4975-9242-38255e99cc07

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_agreePart
import Definitions.Def_GrothendieckLB_disagreePart
import Definitions.Def_GrothendieckLB_B1
import Definitions.Def_GrothendieckLB_D1

open MeasureTheory ProbabilityTheory Real Filter Finset
open GrothendieckLB

-- Gaussian polynomial integrability from LG's checked proof of the symmetric case.
namespace GaussianMomentBounds

noncomputable def phiK (k : ℕ) (x : Fin k → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma phiK_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ phiK k x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma measurable_phiK (k : ℕ) : Measurable (phiK k) := by
  unfold phiK
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

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

def H3 {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) : ℝ :=
  x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
    - (if j = l then x i else 0)

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

lemma measurable_H3 {k : ℕ} (i j l : Fin k) : Measurable fun x : Fin k → ℝ => H3 x i j l := by
  have hite : ∀ (P : Prop) [Decidable P] (m : Fin k),
      Measurable fun x : Fin k → ℝ => if P then x m else 0 := by
    intro P _ m
    by_cases hP : P <;> simp [hP]; fun_prop
  unfold H3
  exact ((((measurable_pi_apply i).mul (measurable_pi_apply j)).mul
    (measurable_pi_apply l)).sub (hite _ l)).sub (hite _ j) |>.sub (hite _ i)

lemma integrable_mom1 {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i : Fin k) : Integrable (fun x => h x * x i * phiK k x) :=
  integrable_poly_phi h (fun x => x i) hh hb (measurable_pi_apply i) 1 zero_le_one
    fun x => abs_coord_le3 x i

lemma integrable_mom3 {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i j l : Fin k) : Integrable (fun x => h x * H3 x i j l * phiK k x) :=
  integrable_poly_phi h (fun x => H3 x i j l) hh hb (measurable_H3 i j l) 4 (by norm_num)
    fun x => abs_H3_le x i j l

end GaussianMomentBounds

open GaussianMomentBounds

private lemma moment_parts {d : ℕ} (f g p : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun x => f x * p x * phiK d x))
    (hg : Integrable (fun x => g x * p x * phiK d x)) :
    gaussExp (fun x => agreePart f g x * p x) =
      (gaussExp (fun x => f x * p x) + gaussExp (fun x => g x * p x)) / 2 ∧
    gaussExp (fun x => disagreePart f g x * p x) =
      (gaussExp (fun x => f x * p x) - gaussExp (fun x => g x * p x)) / 2 := by
  let F := fun x => f x * p x * phiK d x
  let G := fun x => g x * p x * phiK d x
  have hplus (x) : (f x + g x) / 2 * p x * phiK d x = (F x + G x) / 2 := by
    dsimp [F, G]
    ring
  have hminus (x) : (f x - g x) / 2 * p x * phiK d x = (F x - G x) / 2 := by
    dsimp [F, G]
    ring
  change ((∫ x, (f x + g x) / 2 * p x * phiK d x) = ((∫ x, F x) + ∫ x, G x) / 2) ∧
    ((∫ x, (f x - g x) / 2 * p x * phiK d x) = ((∫ x, F x) - ∫ x, G x) / 2)
  constructor
  · simp only [hplus, integral_div, integral_add (f := F) (g := G) hf hg]
  · simp only [hminus, integral_div, integral_sub (f := F) (g := G) hf hg]

private lemma p1Norm_sq {d : ℕ} (u : (Fin d → ℝ) → ℝ) : p1Norm u ^ 2 = p1Inner u u :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

theorem solution {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    B1 f g ≤ D1 (agreePart f g) (disagreePart f g) := by
  let h := agreePart f g
  let k := disagreePart f g
  have bounded {u : (Fin d → ℝ) → ℝ} (hu : IsSignFn u) (x) : |u x| ≤ 1 := by
    rcases hu.2 x with hx | hx <;> simp [hx]
  have h1 (i : Fin d) : linearMoment h i = (linearMoment f i + linearMoment g i) / 2 :=
    (moment_parts f g (fun x => x i)
      (integrable_mom1 f hf.1 (bounded hf) i) (integrable_mom1 g hg.1 (bounded hg) i)).1
  have h3 (i j l : Fin d) :
      cubicMoment h i j l = (cubicMoment f i j l + cubicMoment g i j l) / 2 ∧
      cubicMoment k i j l = (cubicMoment f i j l - cubicMoment g i j l) / 2 :=
    moment_parts f g (fun x => H3 x i j l)
      (integrable_mom3 f hf.1 (bounded hf) i j l) (integrable_mom3 g hg.1 (bounded hg) i j l)
  have linear : 4 * p1Inner h h = p1Inner f f + p1Inner g g + 2 * p1Inner f g := by
    simp only [p1Inner, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1]
    ring
  have cubic : p3NormSq h - p3NormSq k = p3Inner f g := by
    unfold p3NormSq p3Inner
    rw [← mul_sub]
    apply congrArg (fun z : ℝ => (1 / 6) * z)
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [(h3 i j l).1, (h3 i j l).2]
    ring
  change p1Norm f * p1Norm g + p1Inner f g - p3Inner f g ≤
    2 * p1Norm h ^ 2 - p3NormSq h + p3NormSq k
  nlinarith only [linear, cubic, p1Norm_sq h, p1Norm_sq f, p1Norm_sq g,
    sq_nonneg (p1Norm f - p1Norm g)]
