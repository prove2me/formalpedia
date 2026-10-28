-- Prove2me | solution 1 for OAI.SKGap.GaussianHistory.poincare_of_history_estimates_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:15.160383+00:00
-- url     : https://prove2.me/submissions/3d58ee1b-6eeb-4145-ae67-e0383b2a69c1

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_FiniteSpinCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

section FiniteSpinCalculus

variable {n : ℕ}

theorem sum_flip (i : Fin n) (f : Spin n → ℝ) : ∑ x, f (flip i x) = ∑ x, f x :=
  (flipEquiv i).sum_comp f

end FiniteSpinCalculus

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Reference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

lemma integrable_exp_linear (a : Fin n → ℝ) :
    Integrable (fun z => exp (∑ i, a i * z i)) (reference n) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a i))

lemma integral_exp_linear (a : Fin n → ℝ) :
    (∫ z, exp (∑ i, a i * z i) ∂reference n) = exp ((∑ i, (a i)^2) / 2) := by
  simp_rw [exp_sum]
  rw [reference, integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  have hi (i : Fin n) : (∫ z : ℝ, exp (a i * z) ∂gaussianReal 0 1) = exp ((a i)^2/2) := by
    simpa only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add, id_eq] using
      mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1) (by simp) (a i)
  simp_rw [hi]
  rw [← exp_sum, Finset.sum_div]

lemma integrable_likelihood (t : ℝ) (x : Spin n) :
    Integrable (likelihood t x) (reference n) := by
  have he : likelihood t x = fun z => exp (∑ i, (sqrt t * spinValue (x i)) * z i) *
      exp (-(t*n/2)) := by
    funext z
    simp only [likelihood, exp_sub, exp_neg, ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : Spin n) :
    (∫ z, likelihood t x z ∂reference n) = 1 := by
  have he : likelihood t x = fun z => exp (∑ i, (sqrt t * spinValue (x i)) * z i) *
      exp (-(t*n/2)) := by
    funext z
    simp only [likelihood, exp_sub, exp_neg, ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  rw [he, integral_mul_const, integral_exp_linear, ← exp_add]
  have hs : (∑ i, (sqrt t * spinValue (x i)) ^ 2) = t*n := by
    simp [mul_pow, sq_sqrt ht, spinValue_sq, mul_comm]
  rw [hs]
  simp

lemma integrable_density (p : Prior n) (t : ℝ) :
    Integrable (density p t) (reference n) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul (p x))

lemma integral_density (p : Prior n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density p t z ∂reference n) = 1 := by
  change (∫ z, ∑ x, p x * likelihood t x z ∂reference n) = 1
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  exact p.sum_one

lemma mean_abs_le_one (p : Prior n) (i : Fin n) : |mean p i| ≤ 1 := by
  calc
    |mean p i| ≤ ∑ x, |p x * spinValue (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]
      have hs : |spinValue (x i)| = 1 := by cases x i <;> norm_num [spinValue]
      rw [hs, mul_one]
    _ = 1 := p.sum_one

lemma interaction_abs_le (p : Prior n) (x y : Spin n) :
    |interaction p x y| ≤ 4*n := by
  have hl : (0 : ℝ) ≤ ∑ i : Fin n, (spinValue (x i) + spinValue (y i) - mean p i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hu : (∑ i : Fin n, (spinValue (x i) + spinValue (y i) - mean p i)^2) ≤ 9*n := by
    calc
      _ ≤ ∑ _i : Fin n, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hx : |spinValue (x i)| = 1 := by cases x i <;> norm_num [spinValue]
        have hy : |spinValue (y i)| = 1 := by cases y i <;> norm_num [spinValue]
        have hb : |spinValue (x i) + spinValue (y i) - mean p i| ≤ 3 := by
          calc
            _ ≤ |spinValue (x i) + spinValue (y i)| + |mean p i| := abs_sub _ _
            _ ≤ |spinValue (x i)| + |spinValue (y i)| + |mean p i| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ ≤ 3 := by rw [hx, hy]; linarith [mean_abs_le_one p i]
        have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)).mpr hb
        simpa only [sq_abs, show (3:ℝ)^2 = 9 by norm_num] using hh
      _ = 9*n := by simp [mul_comm]
  rw [abs_le]
  unfold interaction
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma interaction_remainder_bound (p : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) (x y : Spin n) :
    |exp (t * interaction p x y) - 1 - t * interaction p x y| ≤
      16*(n:ℝ)^2*t^2 := by
  have hb := interaction_abs_le p x y
  have htb : |t * interaction p x y| ≤ 4*(n:ℝ)*t := by
    rw [abs_mul, abs_of_nonneg ht]
    nlinarith [mul_le_mul_of_nonneg_left hb ht]
  apply (abs_exp_sub_one_sub_id_le (htb.trans htn)).trans
  have hs := sq_le_sq₀ (abs_nonneg (t * interaction p x y)) (by positivity) |>.mpr htb
  simpa only [sq_abs] using (hs.trans_eq (by ring : (4*(n:ℝ)*t)^2 = 16*(n:ℝ)^2*t^2))

lemma interaction_sum (p : Prior n) (x y : Spin n) :
    interaction p x y = ∑ i, ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := by
  have ha : interaction p x y = ∑ i, ((spinValue (x i) + spinValue (y i) - mean p i)^2 - 1)/2 := by
    unfold interaction
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  rw [ha]
  apply Finset.sum_congr rfl
  intro i _
  nlinarith [spinValue_sq (x i), spinValue_sq (y i)]

lemma signed_sum_left (a u : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x * a y * u x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  calc
    _ = (a x * u x) * ∑ y, a y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = 0 := by rw [ha, mul_zero]

lemma signed_sum_right (a u : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x * a y * u y) = 0 := by
  rw [Finset.sum_comm]
  convert signed_sum_left a u ha using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma signed_sum_product (a u : Spin n → ℝ) :
    (∑ x, ∑ y, a x * a y * (u x * u y)) = (∑ x, a x*u x)^2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma signed_interaction (p : Prior n) (a : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*interaction p x y) =
      ∑ i, (∑ x, a x*spinValue (x i))^2 := by
  simp_rw [interaction_sum, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ i, ∑ y, a x*a y* ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, a x*a y* ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [signed_sum_left a (fun _ => (1/2 : ℝ)) ha,
        signed_sum_product a (fun x => spinValue (x i)),
        signed_sum_left a (fun x => spinValue (x i)*mean p i) ha,
        signed_sum_right a (fun y => spinValue (y i)*mean p i) ha,
        signed_sum_left a (fun _ => (mean p i)^2/2) ha]
      ring

lemma integrable_pairKernel (p : Prior n) (t : ℝ) (x y : Spin n) :
    Integrable (pairKernel p t x y) (reference n) := by
  have he : pairKernel p t x y = fun z =>
      exp (∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) *
        exp (-(t*n/2)) := by funext z; simp [pairKernel, exp_sub, exp_neg, div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_pairKernel (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (x y : Spin n) :
    (∫ z, pairKernel p t x y z ∂reference n) = exp (t*interaction p x y) := by
  have he : pairKernel p t x y = fun z =>
      exp (∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) *
        exp (-(t*n/2)) := by funext z; simp [pairKernel, exp_sub, exp_neg, div_eq_mul_inv]
  rw [he, integral_mul_const, integral_exp_linear, ← exp_add]
  congr 1
  simp only [mul_pow, sq_sqrt ht, ← Finset.mul_sum, interaction]
  ring

lemma likelihood_pair (p : Prior n) (t : ℝ) (x y : Spin n) (z : Fin n → ℝ) :
    likelihood t x z * likelihood t y z *
      exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2)) = pairKernel p t x y z := by
  unfold likelihood pairKernel
  rw [← exp_add, ← exp_add]
  congr 1
  simp only [add_mul, sub_mul, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  ring

lemma majorant_eq_sum (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    majorant p a t z = ∑ x, ∑ y, (a x*a y)*pairKernel p t x y z := by
  unfold majorant
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (a x*a y)*(likelihood t x z*likelihood t y z*
        exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2))) := by ring
    _ = _ := by rw [likelihood_pair]

lemma integrable_majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Integrable (majorant p a t) (reference n) := by
  simp_rw [show majorant p a t = fun z => ∑ x, ∑ y, (a x*a y)*pairKernel p t x y z from
    funext (majorant_eq_sum p a t)]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel p t x y).const_mul _))

lemma integral_majorant (p : Prior n) (a : Spin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, majorant p a t z ∂reference n) = ∑ x, ∑ y, (a x*a y)*exp (t*interaction p x y) := by
  simp_rw [majorant_eq_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel p t x y).const_mul _))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => (integrable_pairKernel p t x y).const_mul _)]
  simp_rw [integral_const_mul, integral_pairKernel p ht]

lemma interaction_exp_sum_bound (p : Prior n) (a : Spin n → ℝ)
    (ha : ∑ x, a x = 0) {t : ℝ} (ht : 0 ≤ t) (htn : 4*(n:ℝ)*t ≤ 1) :
    (∑ x, ∑ y, a x*a y*exp (t*interaction p x y)) ≤
      t*(∑ i, (∑ x, a x*spinValue (x i))^2) +
        16*(n:ℝ)^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∑ x, ∑ y, ((a x*a y + t*(a x*a y*interaction p x y)) +
        (16*(n:ℝ)^2*t^2)*(|a x| * |a y|)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hr := interaction_remainder_bound p ht htn x y
      have hb : a x*a y*(exp (t*interaction p x y)-1-t*interaction p x y) ≤
          |a x| * |a y| * (16*(n:ℝ)^2*t^2) := by
        calc
          _ ≤ |a x*a y*(exp (t*interaction p x y)-1-t*interaction p x y)| := le_abs_self _
          _ = |a x| * |a y| * |exp (t*interaction p x y)-1-t*interaction p x y| := by simp [abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      nlinarith only [hb]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [ha, signed_interaction p a ha]
      simp only [mul_zero, Finset.sum_const_zero, zero_add, ← Finset.sum_mul]
      ring

lemma quadraticIntegrand_nonneg (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ quadraticIntegrand p a t z := div_nonneg (sq_nonneg _) (density_pos p t z).le

lemma quadraticIntegrand_le_majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    quadraticIntegrand p a t z ≤ majorant p a t z := by
  unfold quadraticIntegrand
  calc
    _ ≤ (∑ x, a x*likelihood t x z)^2 /
        exp (sqrt t * (∑ i, mean p i*z i) - t*n/2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (exp_pos _) (density_jensen p t z)
    _ = _ := by simp only [majorant, div_eq_mul_inv, exp_neg]

lemma continuous_likelihood (t : ℝ) (x : Spin n) : Continuous (likelihood t x) := by
  unfold likelihood
  fun_prop

lemma continuous_density (p : Prior n) (t : ℝ) : Continuous (density p t) := by
  unfold density
  exact continuous_finsetSum _ (fun x _ => (continuous_likelihood t x).const_mul _)

lemma continuous_quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Continuous (quadraticIntegrand p a t) := by
  apply Continuous.div
    ((continuous_finsetSum _ (fun x _ => (continuous_likelihood t x).const_mul (a x))).pow 2)
    (continuous_density p t)
  intro z
  exact (density_pos p t z).ne'

lemma integrable_quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Integrable (quadraticIntegrand p a t) (reference n) := by
  apply (integrable_majorant p a t).mono' (continuous_quadraticIntegrand p a t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticIntegrand_nonneg p a t z)]
  exact quadraticIntegrand_le_majorant p a t z

theorem quadratic_bound (p : Prior n) (a : Spin n → ℝ) (ha : ∑ x, a x = 0)
    {t : ℝ} (ht : 0 ≤ t) (htn : 4*(n:ℝ)*t ≤ 1) :
    (∫ z, quadraticIntegrand p a t z ∂reference n) ≤
      t*(∑ i, (∑ x, a x*spinValue (x i))^2) +
        16*(n:ℝ)^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∫ z, majorant p a t z ∂reference n :=
      integral_mono (integrable_quadraticIntegrand p a t) (integrable_majorant p a t)
        (quadraticIntegrand_le_majorant p a t)
    _ = _ := integral_majorant p a ht
    _ ≤ _ := interaction_exp_sum_bound p a ha ht htn

lemma var_nonneg (p : Prior n) (f : Spin n → ℝ) : 0 ≤ var p f :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (p.nonneg _) (sq_nonneg _))

lemma avg_const (p : Prior n) (c : ℝ) : avg p (fun _ => c) = c := by
  rw [avg, ← Finset.sum_mul, p.sum_one, one_mul]

lemma avg_sub (p : Prior n) (f g : Spin n → ℝ) :
    avg p (fun x => f x-g x) = avg p f-avg p g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

lemma avg_mul_const (p : Prior n) (f : Spin n → ℝ) (c : ℝ) :
    avg p (fun x => f x*c) = avg p f*c := by
  simp only [avg, mul_assoc, Finset.sum_mul]

lemma avg_center (p : Prior n) (f : Spin n → ℝ) :
    avg p (fun x => f x-avg p f) = 0 := by rw [avg_sub, avg_const, sub_self]

lemma avg_shift_square (p : Prior n) (f : Spin n → ℝ) (c : ℝ) :
    avg p (fun x => (f x-c)^2) = avg p (fun x => (f x)^2)-2*c*avg p f+c^2 := by
  unfold avg
  calc
    _ = ∑ x, ((p x*(f x)^2-(p x*f x)*(2*c))+p x*c^2) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_one]
      ring

end
end SKGap.GaussianStep

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_DivergenceIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

lemma var_eq (p : Prior n) (f : Spin n → ℝ) :
    var p f = avg p (fun x => (f x)^2) - (avg p f)^2 := by
  rw [var, avg_shift_square]
  ring

lemma var_le_square (p : Prior n) (f : Spin n → ℝ) :
    var p f ≤ avg p (fun x => (f x)^2) := by rw [var_eq]; linarith [sq_nonneg (avg p f)]

lemma l1_square_le_avg_square (p : Prior n) (f : Spin n → ℝ) :
    (∑ x, |p x*f x|)^2 ≤ avg p (fun x => (f x)^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => sqrt (p x)) (fun x => sqrt (p x)*|f x|)
  have hs : (∑ x, (sqrt (p x))^2) = 1 := by
    simp_rw [sq_sqrt (p.nonneg _)]; exact p.sum_one
  have he : (∑ x, sqrt (p x)*(sqrt (p x)*|f x|)) = ∑ x, |p x*f x| := by
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc, mul_self_sqrt (p.nonneg x), abs_mul, abs_of_nonneg (p.nonneg x)]
  have hf : (∑ x, (sqrt (p x)*|f x|)^2) = avg p (fun x => (f x)^2) := by
    simp only [avg, mul_pow, sq_sqrt (p.nonneg _), sq_abs]
  rw [he, hs, hf, one_mul] at hc
  exact hc

lemma centered_l1_bound (p : Prior n) (f : Spin n → ℝ) :
    (∑ x, |p x*(f x-avg p f)|)^2 ≤ var p f :=
  l1_square_le_avg_square p (fun x => f x-avg p f)

lemma posterior_avg_weight (p : Prior n) (t : ℝ) (z : Fin n → ℝ) (f : Spin n → ℝ) :
    density p t z * avg (posterior p t z) f = ∑ x, (p x*f x)*likelihood t x z := by
  unfold avg posterior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  field_simp [(density_pos p t z).ne']

lemma integrable_posterior_avg_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) :
    Integrable (fun z => density p t z * avg (posterior p t z) f) (reference n) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul _)

lemma integral_posterior_avg_weight (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∫ z, density p t z * avg (posterior p t z) f ∂reference n) = avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul _)]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  rfl

lemma posterior_variance_identity (p : Prior n) (t : ℝ) (z : Fin n → ℝ) (f : Spin n → ℝ) :
    density p t z * var (posterior p t z) f =
      density p t z * avg (posterior p t z) (fun x => (f x-avg p f)^2) -
        quadraticIntegrand p (fun x => p x*(f x-avg p f)) t z := by
  have ha := posterior_avg_weight p t z (fun x => f x-avg p f)
  have hshift := avg_shift_square (posterior p t z) f (avg p f)
  rw [avg_sub, avg_const] at ha
  rw [var_eq, hshift, quadraticIntegrand, ← ha]
  field_simp [(density_pos p t z).ne']
  ring

lemma integrable_posterior_variance_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) :
    Integrable (fun z => density p t z * var (posterior p t z) f) (reference n) := by
  simp_rw [posterior_variance_identity]
  exact (integrable_posterior_avg_weight p t _).sub (integrable_quadraticIntegrand p _ t)

lemma integral_posterior_variance (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∫ z, density p t z * var (posterior p t z) f ∂reference n) =
      var p f - ∫ z, quadraticIntegrand p (fun x => p x*(f x-avg p f)) t z ∂reference n := by
  simp_rw [posterior_variance_identity]
  rw [integral_sub (integrable_posterior_avg_weight p t _)
    (integrable_quadraticIntegrand p _ t), integral_posterior_avg_weight p ht]
  rfl

theorem variance_step_bound (p : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) (f : Spin n → ℝ) :
    var p f - t*(∑ i, (∑ x, p x*(f x-avg p f)*spinValue (x i))^2) -
        16*(n:ℝ)^2*t^2*var p f ≤
      ∫ z, density p t z*var (posterior p t z) f ∂reference n := by
  rw [integral_posterior_variance p ht]
  have hq := quadratic_bound p (fun x => p x*(f x-avg p f)) (avg_center p f) ht htn
  have he := mul_le_mul_of_nonneg_left (centered_l1_bound p f)
    (show 0 ≤ 16*(n:ℝ)^2*t^2 by positivity)
  linarith

lemma scalar_entropy_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ r*log r-r+1 := by
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hr) hr.le
  have hi : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

lemma scalar_entropy_le_square {r : ℝ} (hr : 0 < r) : r*log r-r+1 ≤ (r-1)^2 := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hr) hr.le
  nlinarith

lemma divergenceIntegrand_eq (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    divergenceIntegrand p q t z = density p t z *
      ((density q t z/density p t z)*log (density q t z/density p t z)-
        density q t z/density p t z+1) := by
  unfold divergenceIntegrand
  field_simp [(density_pos p t z).ne']

lemma divergenceIntegrand_nonneg (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ divergenceIntegrand p q t z := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos p t z).le
    (scalar_entropy_nonneg (div_pos (density_pos q t z) (density_pos p t z)))

lemma density_sub (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    (∑ x, (q x-p x)*likelihood t x z) = density q t z-density p t z := by
  simp only [sub_mul, Finset.sum_sub_distrib, density]

lemma divergenceIntegrand_le_quadratic (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    divergenceIntegrand p q t z ≤ quadraticIntegrand p (fun x => q x-p x) t z := by
  rw [divergenceIntegrand_eq, quadraticIntegrand, density_sub]
  calc
    _ ≤ density p t z*(density q t z/density p t z-1)^2 :=
      mul_le_mul_of_nonneg_left
        (scalar_entropy_le_square (div_pos (density_pos q t z) (density_pos p t z)))
        (density_pos p t z).le
    _ = _ := by field_simp [(density_pos p t z).ne']

lemma continuous_divergenceIntegrand (p q : Prior n) (t : ℝ) :
    Continuous (divergenceIntegrand p q t) := by
  have hd := (continuous_density q t).div (continuous_density p t)
    (fun z => (density_pos p t z).ne')
  exact (((continuous_density q t).mul (hd.log (fun z =>
    (div_pos (density_pos q t z) (density_pos p t z)).ne'))).sub
      (continuous_density q t)).add (continuous_density p t)

lemma integrable_divergenceIntegrand (p q : Prior n) (t : ℝ) :
    Integrable (divergenceIntegrand p q t) (reference n) := by
  apply (integrable_quadraticIntegrand p (fun x => q x-p x) t).mono'
    (continuous_divergenceIntegrand p q t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (divergenceIntegrand_nonneg p q t z)]
  exact divergenceIntegrand_le_quadratic p q t z

lemma prior_sub_l1 (p q : Prior n) : (∑ x, |q x-p x|) ≤ 2 := by
  calc
    _ ≤ ∑ x, (q x+p x) := Finset.sum_le_sum (fun x _ => by
      simpa only [abs_of_nonneg (q.nonneg x), abs_of_nonneg (p.nonneg x)] using abs_sub (q x) (p x))
    _ = 2 := by rw [Finset.sum_add_distrib, q.sum_one, p.sum_one]; norm_num

lemma prior_sub_sum (p q : Prior n) : (∑ x, (q x-p x)) = 0 := by
  rw [Finset.sum_sub_distrib, q.sum_one, p.sum_one, sub_self]

theorem entropy_step_bound (p q : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) :
    (∫ z, divergenceIntegrand p q t z ∂reference n) ≤
      t*(∑ i, (mean q i-mean p i)^2)+64*(n:ℝ)^2*t^2 := by
  have hmean : (∑ i, (∑ x, (q x-p x)*spinValue (x i))^2) =
      ∑ i, (mean q i-mean p i)^2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mean]
  have he : (∑ x, |q x-p x|)^2 ≤ 4 := by
    have hl : 0 ≤ ∑ x, |q x-p x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    nlinarith [prior_sub_l1 p q]
  calc
    _ ≤ ∫ z, quadraticIntegrand p (fun x => q x-p x) t z ∂reference n :=
      integral_mono (integrable_divergenceIntegrand p q t) (integrable_quadraticIntegrand p _ t)
        (divergenceIntegrand_le_quadratic p q t)
    _ ≤ t*(∑ i, (mean q i-mean p i)^2)+16*(n:ℝ)^2*t^2*(∑ x, |q x-p x|)^2 := by
      simpa only [hmean] using quadratic_bound p (fun x => q x-p x) (prior_sub_sum p q) ht htn
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 16*(n:ℝ)^2*t^2 by positivity)]

lemma integrable_relativeEntropy (p q : Prior n) (t : ℝ) :
    Integrable (fun z => density q t z*log (density q t z/density p t z)) (reference n) := by
  have he : (fun z => density q t z*log (density q t z/density p t z)) =
      fun z => divergenceIntegrand p q t z+density q t z-density p t z := by
    funext z
    unfold divergenceIntegrand
    ring
  rw [he]
  exact ((integrable_divergenceIntegrand p q t).add (integrable_density q t)).sub
    (integrable_density p t)

lemma integral_relativeEntropy (p q : Prior n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density q t z*log (density q t z/density p t z) ∂reference n) =
      ∫ z, divergenceIntegrand p q t z ∂reference n := by
  have hi := integral_add
    ((integrable_relativeEntropy p q t).sub (integrable_density q t)) (integrable_density p t)
  have hj := integral_sub (integrable_relativeEntropy p q t) (integrable_density q t)
  simp only [Pi.sub_apply] at hi hj
  rw [hj, integral_density q ht, integral_density p ht] at hi
  change (∫ z, divergenceIntegrand p q t z ∂reference n) = _ at hi
  linarith

lemma avg_add (p : Prior n) (f g : Spin n → ℝ) :
    avg p (fun x => f x+g x) = avg p f+avg p g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

lemma avg_const_mul (p : Prior n) (c : ℝ) (f : Spin n → ℝ) :
    avg p (fun x => c*f x) = c*avg p f := by
  simpa only [mul_comm c] using avg_mul_const p f c

lemma avg_nonneg (p : Prior n) (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

lemma cond_flip (p : Prior n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    cond p i f (flip i x) = cond p i f x := by
  simp only [cond, flip_flip, add_comm]

lemma avg_flip (p : Prior n) (i : Fin n) (f : Spin n → ℝ) :
    avg p f = (1/2:ℝ)*∑ x, (p x*f x+p (flip i x)*f (flip i x)) := by
  rw [Finset.sum_add_distrib, sum_flip i (fun x => p x*f x)]
  unfold avg
  ring

lemma conditional_orthogonal (p : Prior n) (hp : ∀ x, 0 < p x) (i : Fin n)
    (f c : Spin n → ℝ) (hc : ∀ x, c (flip i x)=c x) :
    avg p (fun x => (f x-cond p i f x)*c x) = 0 := by
  rw [avg_flip p i]
  have hs : (∑ x, (p x*((f x-cond p i f x)*c x)+
      p (flip i x)*((f (flip i x)-cond p i f (flip i x))*c (flip i x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [cond_flip, hc]
    unfold cond
    field_simp [(add_pos (hp x) (hp (flip i x))).ne']
    ring
  rw [hs, mul_zero]

lemma conditional_minimal (p : Prior n) (hp : ∀ x, 0 < p x) (i : Fin n)
    (f c : Spin n → ℝ) (hc : ∀ x, c (flip i x)=c x) :
    avg p (fun x => (f x-cond p i f x)^2) ≤ avg p (fun x => (f x-c x)^2) := by
  have ho := conditional_orthogonal p hp i f (fun x => cond p i f x-c x)
    (fun x => by rw [cond_flip, hc])
  have he (x : Spin n) : (f x-c x)^2 =
      (f x-cond p i f x)^2+(cond p i f x-c x)^2+
        2*((f x-cond p i f x)*(cond p i f x-c x)) := by ring
  simp_rw [he]
  rw [avg_add, avg_add, avg_const_mul, ho, mul_zero, add_zero]
  exact le_add_of_nonneg_right (avg_nonneg p _ (fun _ => sq_nonneg _))

lemma energy_nonneg (p : Prior n) (f : Spin n → ℝ) : 0 ≤ energy p f :=
  Finset.sum_nonneg (fun _ _ => avg_nonneg p _ (fun _ => sq_nonneg _))

lemma avg_sum (p : Prior n) {ι : Type*} [Fintype ι] (f : ι → Spin n → ℝ) :
    avg p (fun x => ∑ i, f i x) = ∑ i, avg p (f i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end SKGap.GaussianStep

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Posterior_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma continuous_likelihood (t : ℝ) (x : Spin n) : ∀ k,
    Continuous (likelihood t x (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_likelihood t x k).comp continuous_fst |>.mul
      ((GaussianStep.continuous_likelihood t x).comp continuous_snd)

lemma integrable_likelihood (t : ℝ) (x : Spin n) : ∀ k,
    Integrable (likelihood t x (k := k)) (reference n k)
  | 0 => by
    change Integrable (fun _ : Unit => (1:ℝ)) (Measure.dirac ())
    exact integrable_const 1
  | k+1 => (integrable_likelihood t x k).mul_prod (GaussianStep.integrable_likelihood t x)

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : Spin n) : ∀ k,
    (∫ h : History n k, likelihood t x h ∂reference n k) = 1
  | 0 => by
    change (∫ _ : Unit, (1:ℝ) ∂Measure.dirac ()) = 1
    rw [integral_dirac]
  | k+1 => by
    change (∫ h, likelihood t x h.1 * GaussianStep.likelihood t x h.2
      ∂(reference n k).prod (GaussianStep.reference n)) = 1
    rw [integral_prod_mul, integral_likelihood ht x k, GaussianStep.integral_likelihood ht, mul_one]

lemma continuous_density (p : Prior n) (t : ℝ) (k : ℕ) : Continuous (density p t (k := k)) :=
  continuous_finsetSum _ (fun x _ => (continuous_likelihood t x k).const_mul (p x))

lemma integrable_density (p : Prior n) (t : ℝ) (k : ℕ) :
    Integrable (density p t (k := k)) (reference n k) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood t x k).const_mul (p x))

lemma integral_density (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (∫ h : History n k, density p t h ∂reference n k) = 1 := by
  unfold density
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x k).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  exact p.sum_one

lemma density_zero (p : Prior n) (t : ℝ) (h : History n 0) : density p t h=1 := by
  simp only [density, likelihood, mul_one, p.sum_one]

lemma posterior_zero (p : Prior n) (t : ℝ) (h : History n 0) : posterior p t h=p := by
  apply Prior.ext
  funext x
  change p x*1/density p t h=p x
  rw [density_zero, mul_one, div_one]

lemma density_succ (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    density p t (k := k+1) (h,z) = density p t h*GaussianStep.density (posterior p t h) t z := by
  change (∑ x, p x*(likelihood t x h*GaussianStep.likelihood t x z)) =
    density p t h*(∑ x, (p x*likelihood t x h/density p t h)*GaussianStep.likelihood t x z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos p t h).ne']

lemma posterior_succ (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    posterior p t (k := k+1) (h,z) = GaussianStep.posterior (posterior p t h) t z := by
  apply Prior.ext
  funext x
  change p x*(likelihood t x h*GaussianStep.likelihood t x z)/density p t (k := k+1) (h,z) =
    (p x*likelihood t x h/density p t h)*GaussianStep.likelihood t x z /
      GaussianStep.density (posterior p t h) t z
  rw [density_succ]
  field_simp [(density_pos p t h).ne', (GaussianStep.density_pos (posterior p t h) t z).ne']

lemma integrable_posterior_avg_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) (k : ℕ) :
    Integrable (fun h : History n k => density p t h*avg (posterior p t h) f) (reference n k) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => ((integrable_likelihood t x k).const_mul (p x)).mul_const (f x))

lemma integral_posterior_avg_weight (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) (k : ℕ) :
    (∫ h : History n k, density p t h*avg (posterior p t h) f ∂reference n k)=avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => ((integrable_likelihood t x k).const_mul (p x)).mul_const (f x))]
  simp_rw [integral_mul_const, integral_const_mul, integral_likelihood ht, mul_one]
  rfl

lemma density_le (p q : Prior n) {B : ℝ} (hB : ∀x, q x ≤ B*p x)
    (t : ℝ) {k : ℕ} (h : History n k) : density q t h ≤ B*density p t h := by
  unfold density
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hB x) (likelihood_pos t x h).le)

lemma exists_domination (p q : Prior n) (hp : ∀x,0<p x) :
    ∃B:ℝ,0≤B ∧ ∀x,q x≤B*p x := by
  let B := ∑x,q x/p x
  have hnonneg (x : Spin n) : 0≤q x/p x := div_nonneg (q.nonneg x) (hp x).le
  refine ⟨B,Finset.sum_nonneg (fun x _ => hnonneg x),?_⟩
  intro x
  have hle : q x/p x ≤ B := Finset.single_le_sum (fun y _ => hnonneg y) (Finset.mem_univ x)
  exact (div_le_iff₀ (hp x)).mp hle

lemma divergenceIntegrand_eq (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    divergenceIntegrand p q t h = density p t h*
      ((density q t h/density p t h)*log (density q t h/density p t h)-
        density q t h/density p t h+1) := by
  unfold divergenceIntegrand relativeEntropyIntegrand
  field_simp [(density_pos p t h).ne']

lemma divergenceIntegrand_nonneg (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0≤divergenceIntegrand p q t h := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos p t h).le
    (scalar_entropy_nonneg (div_pos (density_pos q t h) (density_pos p t h)))

lemma continuous_log_ratio (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (fun h : History n k => log (density q t h/density p t h)) :=
  ((continuous_density q t k).div (continuous_density p t k)
    (fun h => (density_pos p t h).ne')).log
      (fun h => (div_pos (density_pos q t h) (density_pos p t h)).ne')

lemma continuous_relativeEntropyIntegrand (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (relativeEntropyIntegrand p q t (k := k)) :=
  (continuous_density q t k).mul (continuous_log_ratio p q t k)

lemma continuous_divergenceIntegrand (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (divergenceIntegrand p q t (k := k)) :=
  ((continuous_relativeEntropyIntegrand p q t k).sub (continuous_density q t k)).add
    (continuous_density p t k)

lemma integrable_divergenceIntegrand (p q : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ) :
    Integrable (divergenceIntegrand p q t (k := k)) (reference n k) := by
  obtain ⟨B,hB,hdom⟩:=exists_domination p q hp
  apply ((integrable_density p t k).mul_const ((B+1)^2)).mono'
    (continuous_divergenceIntegrand p q t k).aestronglyMeasurable
  filter_upwards [] with h
  change |divergenceIntegrand p q t h|≤density p t h*(B+1)^2
  rw [abs_of_nonneg (divergenceIntegrand_nonneg p q t h), divergenceIntegrand_eq]
  apply mul_le_mul_of_nonneg_left _ (density_pos p t h).le
  have hr : 0<density q t h/density p t h := div_pos (density_pos q t h) (density_pos p t h)
  have hle : density q t h/density p t h≤B :=
    (div_le_iff₀ (density_pos p t h)).mpr (density_le p q hdom t h)
  exact (scalar_entropy_le_square hr).trans (by nlinarith)

lemma integrable_relativeEntropyIntegrand (p q : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ) :
    Integrable (relativeEntropyIntegrand p q t (k := k)) (reference n k) := by
  have hi := ((integrable_divergenceIntegrand p q hp t k).add (integrable_density q t k)).sub
    (integrable_density p t k)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  simp only [Pi.sub_apply,Pi.add_apply,divergenceIntegrand]
  ring

lemma entropy_eq_divergence (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    entropy p q t k = ∫h:History n k,divergenceIntegrand p q t h ∂reference n k := by
  have hi := integral_add
    ((integrable_relativeEntropyIntegrand p q hp t k).sub (integrable_density q t k))
    (integrable_density p t k)
  have hj := integral_sub (integrable_relativeEntropyIntegrand p q hp t k)
    (integrable_density q t k)
  simp only [Pi.sub_apply] at hi hj
  rw [hj,integral_density p ht,integral_density q ht] at hi
  change (∫h:History n k,divergenceIntegrand p q t h ∂reference n k) = _ at hi
  change (∫h:History n k,relativeEntropyIntegrand p q t h ∂reference n k) = _
  linarith

lemma entropy_zero (p q : Prior n) (t : ℝ) : entropy p q t 0=0 := by
  unfold entropy relativeEntropyIntegrand
  simp only [density_zero,div_self one_ne_zero,log_one,mul_zero,integral_zero]

lemma integrable_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ} (F : History n k → ℝ)
    (hF : Measurable F) (hi : Integrable (fun h => density p t h*F h) (reference n k)) :
    Integrable (fun h : History n (k+1) => density p t h*F h.1) (reference n (k+1)) := by
  change Integrable (fun h : History n k × (Fin n → ℝ) => density p t (k := k+1) h*F h.1)
    ((reference n k).prod (GaussianStep.reference n))
  apply (integrable_prod_iff (((continuous_density p t (k+1)).measurable.mul
    (hF.comp measurable_fst)).aestronglyMeasurable)).mpr
  constructor
  · filter_upwards [] with h
    change Integrable (fun z => density p t (k := k+1) (h,z)*F h) (GaussianStep.reference n)
    simp_rw [density_succ]
    have he : (fun z => density p t h*GaussianStep.density (posterior p t h) t z*F h) =
        fun z => (density p t h*F h)*GaussianStep.density (posterior p t h) t z := by
      funext z; ring
    rw [he]
    exact (GaussianStep.integrable_density (posterior p t h) t).const_mul _
  · have he (h : History n k) :
        (∫z, ‖density p t (k := k+1) (h,z)*F h‖ ∂GaussianStep.reference n) = ‖density p t h*F h‖ := by
      simp_rw [density_succ,Real.norm_eq_abs,abs_mul,abs_of_pos (density_pos p t h),
        abs_of_pos (GaussianStep.density_pos (posterior p t h) t _)]
      rw [integral_mul_const,integral_const_mul,GaussianStep.integral_density _ ht]
      ring
    change Integrable (fun h : History n k =>
      ∫z, ‖density p t (k := k+1) (h,z)*F h‖ ∂GaussianStep.reference n) (reference n k)
    simp_rw [he]
    exact hi.norm

lemma integral_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ} (F : History n k → ℝ)
    (hF : Measurable F) (hi : Integrable (fun h => density p t h*F h) (reference n k)) :
    (∫h:History n (k+1),density p t h*F h.1 ∂reference n (k+1)) =
      ∫h:History n k,density p t h*F h ∂reference n k := by
  rw [show reference n (k+1)=(reference n k).prod (GaussianStep.reference n) from rfl,
    integral_prod _ (integrable_lift p ht F hF hi)]
  apply integral_congr_ae
  filter_upwards [] with h
  simp_rw [density_succ]
  rw [integral_mul_const,integral_const_mul,GaussianStep.integral_density _ ht,mul_one]

lemma relativeEntropy_succ (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    relativeEntropyIntegrand p q t (k := k+1) (h,z) =
      density q t (k := k+1) (h,z)*log (density q t h/density p t h)+
      density q t h*(GaussianStep.density (posterior q t h) t z *
        log (GaussianStep.density (posterior q t h) t z/GaussianStep.density (posterior p t h) t z)) := by
  unfold relativeEntropyIntegrand
  rw [density_succ,density_succ]
  rw [mul_div_mul_comm,log_mul
    (div_pos (density_pos q t h) (density_pos p t h)).ne'
    (div_pos (GaussianStep.density_pos (posterior q t h) t z)
      (GaussianStep.density_pos (posterior p t h) t z)).ne']
  ring

theorem entropy_succ (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    entropy p q t (k+1) = entropy p q t k+
      ∫h:History n k,density q t h*
        (∫z,GaussianStep.divergenceIntegrand (posterior p t h) (posterior q t h) t z
          ∂GaussianStep.reference n) ∂reference n k := by
  let L : History n k → ℝ := fun h => log (density q t h/density p t h)
  have hL : Measurable L := (continuous_log_ratio p q t k).measurable
  have hiL : Integrable (fun h => density q t h*L h) (reference n k) :=
    integrable_relativeEntropyIntegrand p q hp t k
  have hLift := integrable_lift q ht L hL hiL
  have hi := (integrable_relativeEntropyIntegrand p q hp t (k+1)).sub hLift
  have he : (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz - density q t hz*L hz.1) =
      fun hz => density q t hz.1*(GaussianStep.density (posterior q t hz.1) t hz.2*
        log (GaussianStep.density (posterior q t hz.1) t hz.2/GaussianStep.density (posterior p t hz.1) t hz.2)) := by
    funext ⟨h,z⟩
    rw [relativeEntropy_succ]
    dsimp [L]
    ring
  have hs := integral_sub (integrable_relativeEntropyIntegrand p q hp t (k+1)) hLift
  change (∫hz:History n (k+1),relativeEntropyIntegrand p q t hz-density q t hz*L hz.1
    ∂reference n (k+1)) = _ at hs
  rw [integral_lift q ht L hL hiL] at hs
  change (∫hz:History n (k+1),relativeEntropyIntegrand p q t hz-density q t hz*L hz.1
    ∂reference n (k+1)) = entropy p q t (k+1)-entropy p q t k at hs
  change Integrable (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-
    density q t hz*L hz.1) (reference n (k+1)) at hi
  rw [he] at hi hs
  rw [show reference n (k+1)=(reference n k).prod (GaussianStep.reference n) from rfl,
    integral_prod _ hi] at hs
  simp_rw [integral_const_mul,GaussianStep.integral_relativeEntropy _ _ ht] at hs
  linarith

lemma scalar_entropy_fenchel {r : ℝ} (hr : 0 < r) (c : ℝ) :
    c*r-exp c+1 ≤ r*log r-r+1 := by
  have he := mul_le_mul_of_nonneg_left (add_one_le_exp (c-log r)) hr.le
  have hx : r*exp (c-log r)=exp c := by
    rw [exp_sub,exp_log hr]
    field_simp
  rw [hx] at he
  nlinarith

theorem entropy_event_bound (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (k : ℕ) (E : Set (History n k)) (hE : MeasurableSet E) (c : ℝ)
    (hsmall : eventProbability p t E≤exp (-c)) :
    c*eventProbability q t E ≤ entropy p q t k+1 := by
  have hpoint (h : History n k) :
      c*E.indicator (density q t) h ≤ divergenceIntegrand p q t h+
        exp c*E.indicator (density p t) h := by
    by_cases he : h∈E
    · rw [Set.indicator_of_mem he,Set.indicator_of_mem he,divergenceIntegrand_eq]
      have hf := mul_le_mul_of_nonneg_left
        (scalar_entropy_fenchel (div_pos (density_pos q t h) (density_pos p t h)) c)
        (density_pos p t h).le
      have hd : density p t h*(density q t h/density p t h)=density q t h :=
        mul_div_cancel₀ _ (density_pos p t h).ne'
      have hmul : density p t h*(c*(density q t h/density p t h))=c*density q t h := by
        rw [←mul_assoc, mul_comm (density p t h) c,mul_assoc,hd]
      nlinarith [density_pos p t h]
    · rw [Set.indicator_of_notMem he,Set.indicator_of_notMem he,mul_zero,mul_zero,add_zero]
      exact divergenceIntegrand_nonneg p q t h
  have hi := integral_mono (((integrable_density q t k).indicator hE).const_mul c)
    ((integrable_divergenceIntegrand p q hp t k).add
      (((integrable_density p t k).indicator hE).const_mul (exp c))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (integrable_divergenceIntegrand p q hp t k)
      (((integrable_density p t k).indicator hE).const_mul (exp c)),integral_const_mul,
    integral_indicator hE,integral_indicator hE,←entropy_eq_divergence p q hp ht] at hi
  change c*eventProbability q t E≤entropy p q t k+exp c*eventProbability p t E at hi
  have hm := mul_le_mul_of_nonneg_left hsmall (exp_pos c).le
  rw [←exp_add,add_neg_cancel,exp_zero] at hm
  linarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Brownian_ContinuousPosteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma continuous_posterior_mass (p : Prior n) (t : ℝ) (k : ℕ) (x : Spin n) :
    Continuous (fun h : History n k => posterior p t h x) :=
  ((continuous_likelihood t x k).const_mul (p x)).div (continuous_density p t k)
    (fun h => (density_pos p t h).ne')

lemma continuous_posterior_avg (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Continuous (fun h : History n k => avg (posterior p t h) f) :=
  continuous_finsetSum _ (fun x _ => (continuous_posterior_mass p t k x).mul_const (f x))

lemma continuous_posterior_var (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Continuous (fun h : History n k => var (posterior p t h) f) := by
  simp_rw [var_eq]
  exact (continuous_posterior_avg p t k _).sub ((continuous_posterior_avg p t k f).pow 2)

lemma posterior_mass_pos (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) {k : ℕ} (h : History n k)
    (x : Spin n) : 0<posterior p t h x :=
  div_pos (mul_pos (hp x) (likelihood_pos t x h)) (density_pos p t h)

lemma posterior_energy_bound (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) {k : ℕ} (h : History n k)
    (f : Spin n→ℝ) : energy (posterior p t h) f ≤
      avg (posterior p t h) (fun x => ∑i,(f x-cond p i f x)^2) := by
  rw [avg_sum]
  exact Finset.sum_le_sum (fun i _ => conditional_minimal (posterior p t h)
    (posterior_mass_pos p hp t h) i f (cond p i f) (cond_flip p i f))

lemma continuous_posterior_cond (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    Continuous (fun h : History n k => cond (posterior p t h) i f x) := by
  apply Continuous.div
    (((continuous_posterior_mass p t k x).mul_const (f x)).add
      ((continuous_posterior_mass p t k (flip i x)).mul_const (f (flip i x))))
    ((continuous_posterior_mass p t k x).add (continuous_posterior_mass p t k (flip i x)))
  intro h
  exact (add_pos (posterior_mass_pos p hp t h x) (posterior_mass_pos p hp t h (flip i x))).ne'

lemma continuous_posterior_energy (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (f : Spin n→ℝ) : Continuous (fun h : History n k => energy (posterior p t h) f) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  exact (continuous_posterior_mass p t k x).mul
    ((continuous_const.sub (continuous_posterior_cond p hp t k i f x)).pow 2)

lemma integrable_posterior_energy_weight (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (f : Spin n→ℝ) :
    Integrable (fun h : History n k => density p t h*energy (posterior p t h) f) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => ∑i,(f x-cond p i f x)^2) k).mono'
    ((continuous_density p t k).mul (continuous_posterior_energy p hp t k f)).aestronglyMeasurable
  filter_upwards [] with h
  change |density p t h*energy (posterior p t h) f|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (energy_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t h f) (density_pos p t h).le

theorem energy_history_bound (p : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (k : ℕ) (f : Spin n→ℝ) :
    (∫h:History n k,density p t h*energy (posterior p t h) f ∂reference n k) ≤ energy p f := by
  let F : Spin n→ℝ := fun x => ∑i,(f x-cond p i f x)^2
  have hle : (∫h:History n k,density p t h*energy (posterior p t h) f ∂reference n k) ≤
      ∫h:History n k,density p t h*avg (posterior p t h) F ∂reference n k := by
    apply integral_mono (integrable_posterior_energy_weight p hp t k f)
      (integrable_posterior_avg_weight p t F k)
    intro h
    exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t h f) (density_pos p t h).le
  rw [integral_posterior_avg_weight p ht] at hle
  change _≤avg p (fun x => ∑i,(f x-cond p i f x)^2) at hle
  rw [avg_sum] at hle
  exact hle

lemma weighted_energy_identity (p : Prior n) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) (t : ℝ) {k : ℕ} (h : History n k) :
    density (squarePrior p f hf) t h*
      (energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)) =
        density p t h*energy (posterior p t h) f/avg p (fun x => (f x)^2) := by
  rw [squarePrior_density]
  field_simp [(posterior_square_pos p f hf t h).ne']

lemma mean_difference_square_le (p q : Prior n) :
    (∑i,(mean q i-mean p i)^2)≤4*(n:ℝ) := by
  calc
    _≤∑i:Fin n,(4:ℝ) := Finset.sum_le_sum (fun i _ => by
      have hp:=abs_le.mp (mean_abs_le_one p i)
      have hq:=abs_le.mp (mean_abs_le_one q i)
      nlinarith [sq_nonneg (mean q i-mean p i)])
    _=_ := by simp; ring

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_AffineUpper
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.DiscreteRecurrence
open Real

lemma affine_upper (u : ℕ→ℝ) {b r : ℝ} (hb : 0≤b) (hr : 0 ≤ r)
    (hzero : u 0≤0) (K : ℕ)
    (hstep : ∀k<K,u (k+1)≤(1+b)*u k+r) :
    u K≤(K:ℝ)*r*exp ((K:ℝ)*b) := by
  have hh : ∀ k≤K,u k≤(k:ℝ)*r*(1+b)^k := by
    intro k hk
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hi:=mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hk)) (by linarith : 0≤1+b)
      have hp : 1≤(1+b)^(k+1) := one_le_pow₀ (by linarith)
      have hrp:=mul_le_mul_of_nonneg_left hp hr
      have hs:=hstep k (Nat.lt_of_succ_le hk)
      simp only [Nat.cast_add,Nat.cast_one,pow_succ] at hrp ⊢
      nlinarith
  have hp:=pow_le_pow_left₀ (by linarith : 0≤1+b) (by simpa only [add_comm] using Real.add_one_le_exp b) K
  have hm:=mul_le_mul_of_nonneg_left hp (show 0≤(K:ℝ)*r by positivity)
  rw [←Real.exp_nat_mul] at hm
  simpa only [mul_comm b] using (hh K le_rfl).trans hm

lemma affine_lower (u : ℕ→ℝ) {r b : ℝ} (hr : 0 ≤ r) (hr1 : r≤1) (hb : 0≤b)
    (K : ℕ) (hstep : ∀k<K,r*u k-b≤u (k+1)) :
    r^K*u 0-(K:ℝ)*b≤u K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hi:=mul_le_mul_of_nonneg_left (ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self K)))) hr
    have hs:=hstep K (Nat.lt_succ_self K)
    have hb':=mul_le_mul_of_nonneg_right hr1 (show 0≤(K:ℝ)*b by positivity)
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith

lemma exp_neg_two_le {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) :
    exp (-2*x)≤1-x := by
  have hpos : 0<1-x := by linarith
  have hi : (1-x)⁻¹≤1+2*x := by
    rw [inv_eq_one_div,div_le_iff₀ hpos]
    nlinarith
  have hl:=Real.one_sub_inv_le_log_of_pos hpos
  have hh : -2*x≤log (1-x) := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

lemma pow_one_sub_lower {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) (K : ℕ) :
    exp (-2*(K:ℝ)*x)≤(1-x)^K := by
  have hh:=pow_le_pow_left₀ (exp_pos (-2*x)).le (exp_neg_two_le hx hx1) K
  rw [←Real.exp_nat_mul] at hh
  have he : (K:ℝ)*(-2*x)= -2*(K:ℝ)*x := by ring
  rwa [he] at hh

end SKGap.DiscreteRecurrence

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_DriftSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma driftSquare_nonneg (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0≤driftSquare p q t h := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma driftSquare_le (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    driftSquare p q t h≤4*(n:ℝ) := mean_difference_square_le _ _

lemma continuous_driftSquare (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (driftSquare p q t (k := k)) := by
  unfold driftSquare mean
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_finsetSum _ (fun x _ => (continuous_posterior_mass q t k x).mul_const _)).sub
      (continuous_finsetSum _ (fun x _ => (continuous_posterior_mass p t k x).mul_const _))).pow 2)

lemma integrable_driftSquare_weight (p q : Prior n) (t : ℝ) (k : ℕ) :
    Integrable (fun h : History n k => density q t h*driftSquare p q t h) (reference n k) := by
  apply ((integrable_density q t k).mul_const (4*(n:ℝ))).mono'
    ((continuous_density q t k).mul (continuous_driftSquare p q t k)).aestronglyMeasurable
  filter_upwards [] with h
  change |density q t h*driftSquare p q t h|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos q t h).le (driftSquare_nonneg _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (driftSquare_le p q t h) (density_pos q t h).le

lemma integrable_entropy_increment (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    Integrable (fun h : History n k => density q t h*
      (∫z,GaussianStep.divergenceIntegrand (posterior p t h) (posterior q t h) t z
        ∂GaussianStep.reference n)) (reference n k) := by
  let L : History n k → ℝ := fun h => log (density q t h/density p t h)
  have hL : Measurable L := (continuous_log_ratio p q t k).measurable
  have hiL : Integrable (fun h => density q t h*L h) (reference n k) :=
    integrable_relativeEntropyIntegrand p q hp t k
  have hLift := integrable_lift q ht L hL hiL
  have hi := (integrable_relativeEntropyIntegrand p q hp t (k+1)).sub hLift
  have he : (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-density q t hz*L hz.1) =
      fun hz => density q t hz.1*(GaussianStep.density (posterior q t hz.1) t hz.2*
        log (GaussianStep.density (posterior q t hz.1) t hz.2/GaussianStep.density (posterior p t hz.1) t hz.2)) := by
    funext ⟨h,z⟩
    rw [relativeEntropy_succ]
    dsimp [L]
    ring
  change Integrable (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-
    density q t hz*L hz.1) ((reference n k).prod (GaussianStep.reference n)) at hi
  rw [he] at hi
  have hh := hi.integral_prod_left
  simp_rw [integral_const_mul,GaussianStep.integral_relativeEntropy _ _ ht] at hh
  exact hh

lemma entropy_step_history_bound (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (htn : 4*(n:ℝ)*t≤1) (k : ℕ) :
    entropy p q t (k+1)≤entropy p q t k+
      t*(∫h:History n k,density q t h*driftSquare p q t h ∂reference n k)+64*(n:ℝ)^2*t^2 := by
  rw [entropy_succ p q hp ht]
  have hh := integral_mono (integrable_entropy_increment p q hp ht k)
    (((integrable_driftSquare_weight p q t k).const_mul t).add
      ((integrable_density q t k).mul_const (64*(n:ℝ)^2*t^2)))
      (fun h => (mul_le_mul_of_nonneg_left
        (GaussianStep.entropy_step_bound (posterior p t h) (posterior q t h) ht htn)
        (density_pos q t h).le).trans_eq (by dsimp [driftSquare]; ring))
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_driftSquare_weight p q t k).const_mul t)
      ((integrable_density q t k).mul_const (64*(n:ℝ)^2*t^2)),integral_const_mul,
      integral_mul_const,integral_density q ht,one_mul] at hh
  linarith

lemma drift_integral_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (B : Set (History n k)) (hB : MeasurableSet B) (W A : ℝ) (hW : 0≤W) (hA : 0≤A)
    (hgood : ∀h:History n k,h∉B → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    (∫h:History n k,density (squarePrior p f hf) t h*driftSquare p (squarePrior p f hf) t h ∂reference n k) ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+
        4*(n:ℝ)*eventProbability (squarePrior p f hf) t B := by
  let q:=squarePrior p f hf
  let N:=avg p (fun x => (f x)^2)
  let d : History n k→ℝ := fun h => density p t h*energy (posterior p t h) f
  have hiD : Integrable d (reference n k) := integrable_posterior_energy_weight p hp t k f
  have hiQ := integrable_density q t k
  have hiB := hiQ.indicator hB
  have hpoint (h : History n k) : density q t h*driftSquare p q t h ≤
      (W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+
        (A*sqrt (n:ℝ)/N)*d h+4*(n:ℝ)*B.indicator (density q t) h := by
    have he := weighted_energy_identity p f hf t h
    change density q t h*(energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)) = d h/N at he
    have hd0 : 0≤d h := mul_nonneg (density_pos p t h).le (energy_nonneg _ _)
    have hconst : 0≤(W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h :=
      mul_nonneg (by positivity) (density_pos q t h).le
    have hdpos : 0≤(A*sqrt (n:ℝ)/N)*d h := mul_nonneg (div_nonneg (mul_nonneg hA (sqrt_nonneg _)) hf.le) hd0
    by_cases hb : h∈B
    · rw [Set.indicator_of_mem hb]
      have hh:=mul_le_mul_of_nonneg_left (driftSquare_le p q t h) (density_pos q t h).le
      nlinarith
    · rw [Set.indicator_of_notMem hb,mul_zero,add_zero]
      have hh:=mul_le_mul_of_nonneg_left (hgood h hb) (density_pos q t h).le
      calc
        _≤density q t h*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) := hh
        _=(W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+A*sqrt (n:ℝ)*
            (density q t h*(energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) := by ring
        _=_ := by rw [he]; ring
  have hi1 := hiQ.const_mul (W*(n:ℝ)+2*A*sqrt (n:ℝ))
  have hi2 := hiD.const_mul (A*sqrt (n:ℝ)/N)
  have hi3 := hiB.const_mul (4*(n:ℝ))
  have hi12 : Integrable (fun h => (W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+
      (A*sqrt (n:ℝ)/N)*d h) (reference n k) := hi1.add hi2
  have hh := integral_mono (integrable_driftSquare_weight p q t k) (hi12.add hi3) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hi12 hi3,integral_add hi1 hi2,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_density q ht,integral_indicator hB,mul_one] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f)
    (show 0≤A*sqrt (n:ℝ)/N from div_nonneg (mul_nonneg hA (sqrt_nonneg _)) hf.le)
  change _≤(W*(n:ℝ)+2*A*sqrt (n:ℝ))+(A*sqrt (n:ℝ)/N)*(∫h,d h ∂reference n k)+
    4*(n:ℝ)*eventProbability q t B at hh
  change (A*sqrt (n:ℝ)/N)*(∫h,d h ∂reference n k)≤(A*sqrt (n:ℝ)/N)*energy p f at hd
  dsimp [N,q] at hh hd
  simp only [div_eq_mul_inv] at hh hd ⊢
  nlinarith

theorem entropy_good_step (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (k : ℕ)
    (B : Set (History n k)) (hB : MeasurableSet B) (W A a : ℝ)
    (hW : 0≤W) (hA : 0≤A) (ha : 0<a)
    (hsmall : eventProbability p t B≤exp (-a*(n:ℝ)))
    (hgood : ∀h:History n k,h∉B → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    entropy p (squarePrior p f hf) t (k+1)≤
      (1+4*t/a)*entropy p (squarePrior p f hf) t k+
        t*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*t^2 := by
  have hs:=entropy_step_history_bound p (squarePrior p f hf) hp ht htn k
  have hd:=mul_le_mul_of_nonneg_left (drift_integral_bound p hp f hf ht k B hB W A hW hA hgood) ht
  have he:=entropy_event_bound p (squarePrior p f hf) hp ht k B hB (a*(n:ℝ))
    (by simpa only [neg_mul] using hsmall)
  have he':=mul_le_mul_of_nonneg_left he (show 0≤4*t/a by positivity)
  have heq : (4*t/a)*(a*(n:ℝ)*eventProbability (squarePrior p f hf) t B)=
      t*(4*(n:ℝ)*eventProbability (squarePrior p f hf) t B) := by field_simp
  rw [heq] at he'
  simp only [div_eq_mul_inv] at hs hd he' ⊢
  nlinarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Envelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma envelope_nonneg (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) : 0≤envelope p t A f h := by
  unfold envelope
  split_ifs
  · exact var_nonneg _ _
  · exact avg_nonneg _ _ (fun _ => sq_nonneg _)

lemma var_le_envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) : var (posterior p t h) f≤envelope p t A f h := by
  unfold envelope
  split_ifs
  · rfl
  · exact var_le_square _ _

lemma envelope_le_square (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) :
    envelope p t A f h≤avg (posterior p t h) (fun x => (f x)^2) := by
  unfold envelope
  split_ifs
  · exact var_le_square _ _
  · rfl

lemma measurable_envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (hA : MeasurableSet A) (f : Spin n→ℝ) : Measurable (envelope p t A f) :=
  Measurable.ite hA (continuous_posterior_var p t k f).measurable
    (continuous_posterior_avg p t k _).measurable

lemma integrable_envelope_weight (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (hA : MeasurableSet A) (f : Spin n→ℝ) :
    Integrable (fun h => density p t h*envelope p t A f h) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => (f x)^2) k).mono'
    (((continuous_density p t k).measurable.mul (measurable_envelope p t A hA f)).aestronglyMeasurable)
  filter_upwards [] with h
  change |density p t h*envelope p t A f h|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (envelope_nonneg p t A f h))]
  exact mul_le_mul_of_nonneg_left (envelope_le_square p t A f h) (density_pos p t h).le

lemma variance_le_envelope_zero (p : Prior n) (t : ℝ) (A : Set (History n 0)) (f : Spin n→ℝ) :
    var p f≤envelopeIntegral p t A f := by
  unfold envelopeIntegral reference
  rw [integral_dirac,density_zero,one_mul]
  have hh:=var_le_envelope p t A f ()
  rw [posterior_zero] at hh
  exact hh

lemma integrable_envelope_section (p : Prior n) (t : ℝ) {k : ℕ} (G : Set (History n (k+1)))
    (hG : MeasurableSet G) (f : Spin n→ℝ) (h : History n k) :
    Integrable (fun z => GaussianStep.density (posterior p t h) t z *
      envelope p t G f (h,z)) (GaussianStep.reference n) := by
  have hm : Measurable (fun z => envelope p t G f (h,z)) :=
    (measurable_envelope p t G hG f).comp (measurable_const.prodMk measurable_id)
  have hn : Integrable (fun z => GaussianStep.density (posterior p t h) t z*
      avg (posterior p t (k := k+1) (h,z)) (fun x => (f x)^2)) (GaussianStep.reference n) := by
    simp_rw [posterior_succ]
    exact GaussianStep.integrable_posterior_avg_weight _ t _
  apply hn.mono' (((GaussianStep.continuous_density (posterior p t h) t).measurable.mul hm).aestronglyMeasurable)
  filter_upwards [] with z
  change |GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)|≤_
  rw [abs_of_nonneg (mul_nonneg (GaussianStep.density_pos _ _ _).le (envelope_nonneg _ _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (envelope_le_square p t G f (h,z)) (GaussianStep.density_pos _ _ _).le

lemma envelope_step_point (p : Prior n) (t : ℝ) {k : ℕ}
    (A : Set (History n k)) (G : Set (History n (k+1))) (hG : MeasurableSet G)
    (hprefix : ∀h:History n (k+1),h∈G→h.1∈A) (f : Spin n→ℝ)
    (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (D : ℝ) (hD : 0≤D)
    (hgood : ∀h:History n k,h∈A→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (h : History n k) :
    (1-D*t)*envelope p t A f h-D*t*energy (posterior p t h) f-
        16*(n:ℝ)^2*t^2*avg (posterior p t h) (fun x => (f x)^2) ≤
      ∫z,GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)
        ∂GaussianStep.reference n := by
  by_cases hh : h∈A
  · have hv : (∫z,GaussianStep.density (posterior p t h) t z*
        var (GaussianStep.posterior (posterior p t h) t z) f ∂GaussianStep.reference n) ≤
        ∫z,GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)
          ∂GaussianStep.reference n := by
      apply integral_mono (GaussianStep.integrable_posterior_variance_weight _ t f)
        (integrable_envelope_section p t G hG f h)
      intro z
      have he:=var_le_envelope p t G f (h,z)
      rw [posterior_succ] at he
      exact mul_le_mul_of_nonneg_left he (GaussianStep.density_pos _ _ _).le
    have hs:=GaussianStep.variance_step_bound (posterior p t h) ht htn f
    have hc:=mul_le_mul_of_nonneg_left (hgood h hh) ht
    have hn:=mul_le_mul_of_nonneg_left (var_le_square (posterior p t h) f)
      (show 0≤16*(n:ℝ)^2*t^2 by positivity)
    rw [envelope,ite_eq_left hh]
    nlinarith
  · have he (z : Fin n→ℝ) : envelope p t G f (h,z)=
        avg (GaussianStep.posterior (posterior p t h) t z) (fun x => (f x)^2) := by
      rw [envelope,ite_eq_right (fun hmem => hh (hprefix (h,z) hmem)),posterior_succ]
    simp_rw [he]
    rw [GaussianStep.integral_posterior_avg_weight _ ht,envelope,ite_eq_right hh]
    have hN : 0≤avg (posterior p t h) (fun x => (f x)^2) := avg_nonneg _ _ (fun _ => sq_nonneg _)
    have hE:=energy_nonneg (posterior p t h) f
    have hdt : 0≤D*t := mul_nonneg hD ht
    have herr : 0≤16*(n:ℝ)^2*t^2 := by positivity
    nlinarith [mul_nonneg hdt hN,mul_nonneg hdt hE,mul_nonneg herr hN]

theorem envelope_step_bound (p : Prior n) (hp : ∀x,0<p x) {t : ℝ} {k : ℕ}
    (A : Set (History n k)) (hA : MeasurableSet A)
    (G : Set (History n (k+1))) (hG : MeasurableSet G)
    (hprefix : ∀h:History n (k+1),h∈G→h.1∈A) (f : Spin n→ℝ)
    (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (D : ℝ) (hD : 0≤D)
    (hgood : ∀h:History n k,h∈A→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f)) :
    (1-D*t)*envelopeIntegral p t A f-D*t*energy p f-
        16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2) ≤ envelopeIntegral p t G f := by
  have hi:=integrable_envelope_weight p t G hG f
  change Integrable (fun hz : History n k × (Fin n→ℝ) => density p t (k := k+1) hz*envelope p t G f hz)
    ((reference n k).prod (GaussianStep.reference n)) at hi
  have hiR:=hi.integral_prod_left
  have he : (∫h:History n k,∫z,density p t (k := k+1) (h,z)*envelope p t G f (h,z)
      ∂GaussianStep.reference n ∂reference n k)=envelopeIntegral p t G f :=
    (integral_prod _ hi).symm
  have hi1:=(integrable_envelope_weight p t A hA f).const_mul (1-D*t)
  have hi2:=(integrable_posterior_energy_weight p hp t k f).const_mul (D*t)
  have hi3:=(integrable_posterior_avg_weight p t (fun x => (f x)^2) k).const_mul (16*(n:ℝ)^2*t^2)
  have hi12 : Integrable (fun h => (1-D*t)*(density p t h*envelope p t A f h)-
      D*t*(density p t h*energy (posterior p t h) f)) (reference n k) := hi1.sub hi2
  have hh:=integral_mono (hi12.sub hi3) hiR (fun h => ?_)
  swap
  · simp only [Pi.sub_apply]
    simp_rw [density_succ,mul_assoc]
    rw [integral_const_mul]
    convert mul_le_mul_of_nonneg_left (envelope_step_point p t A G hG hprefix f ht htn D hD hgood h)
      (density_pos p t h).le using 1; ring
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi12 hi3,integral_sub hi1 hi2,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_posterior_avg_weight p ht,he] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f) (mul_nonneg hD ht)
  change (1-D*t)*envelopeIntegral p t A f-D*t*(∫h,density p t h*energy (posterior p t h) f ∂reference n k)-
    16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2)≤envelopeIntegral p t G f at hh
  linarith

theorem envelope_terminal_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) {k : ℕ}
    (A E : Set (History n k)) (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hprefix : Aᶜ⊆E) (L : ℝ) (hL : 0≤L)
    (hterminal : ∀h:History n k,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    envelopeIntegral p t A f≤ L*energy p f+
      avg p (fun x => (f x)^2)*eventProbability (squarePrior p f hf) t E := by
  let N:=avg p (fun x => (f x)^2)
  have hi1:=(integrable_posterior_energy_weight p hp t k f).const_mul L
  have hi2:=((integrable_density (squarePrior p f hf) t k).indicator hE).const_mul N
  have hh:=integral_mono (integrable_envelope_weight p t A hA f) (hi1.add hi2) (fun h => ?_)
  swap
  · simp only [Pi.add_apply]
    by_cases he : h∈E
    · rw [Set.indicator_of_mem he,squarePrior_density]
      have henv:=mul_le_mul_of_nonneg_left (envelope_le_square p t A f h) (density_pos p t h).le
      have hden : N*(density p t h*avg (posterior p t h) (fun x => (f x)^2)/N)=
          density p t h*avg (posterior p t h) (fun x => (f x)^2) := mul_div_cancel₀ _ hf.ne'
      change _≤L*(density p t h*energy (posterior p t h) f)+N*(_/N)
      rw [hden]
      exact henv.trans (le_add_of_nonneg_left (mul_nonneg hL
        (mul_nonneg (density_pos p t h).le (energy_nonneg _ _))))
    · have ha : h∈A := by by_contra hn; exact he (hprefix hn)
      simp only [Set.indicator_of_notMem he,mul_zero,add_zero,envelope,ite_eq_left ha]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hterminal h he) (density_pos p t h).le
  simp only [Pi.add_apply] at hh
  rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul,integral_indicator hE] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f) hL
  change envelopeIntegral p t A f≤L*(∫h,density p t h*energy (posterior p t h) f ∂reference n k)+
    N*eventProbability (squarePrior p f hf) t E at hh
  dsimp [N] at hh
  linarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Entropy_EntropyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep DiscreteRecurrence
noncomputable section
variable {n : ℕ}

lemma entropy_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B : ∀k,Set (History n k)) (hB : ∀k,MeasurableSet (B k))
    (W A a T : ℝ) (hW : 0≤W) (hA : 0≤A) (ha : 0<a) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hgood : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    entropy p (squarePrior p f hf) t K≤
      exp (4*T/a)*(T*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*T*t) := by
  have hh:=affine_upper (entropy p (squarePrior p f hf) t)
    (show 0≤4*t/a by positivity)
    (show 0≤t*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*t^2 by have := energy_nonneg p f; positivity)
    (entropy_zero p (squarePrior p f hf) t).le K
    (fun k hk => by
      simpa only [add_assoc] using entropy_good_step p hp f hf ht htn k (B k) (hB k) W A a hW hA ha
        (hsmall k hk) (hgood k hk))
  have he : (K:ℝ)*(4*t/a)=4*T/a := by rw [←hT]; ring
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [←hT]
  ring

lemma envelope_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (K : ℕ)
    (G : ∀k,Set (History n k)) (hG : ∀k,MeasurableSet (G k))
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (D T : ℝ) (hD : 0≤D) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hgood : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f)) :
    exp (-2*D*T)*var p f≤ envelopeIntegral p t (G K) f+D*T*energy p f+
      16*(n:ℝ)^2*T*t*avg p (fun x => (f x)^2) := by
  have hh:=affine_lower (fun k => envelopeIntegral p t (G k) f)
    (show 0≤1-D*t by linarith) (show 1-D*t≤1 by nlinarith)
    (show 0≤D*t*energy p f+16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2) by
      have := energy_nonneg p f
      have := avg_nonneg p (fun x => (f x)^2) (fun _ => sq_nonneg _)
      positivity) K (fun k hk => by
        have hs:=envelope_step_bound p hp (G k) (hG k) (G (k+1)) (hG (k+1))
          (hprefix k hk) f ht htn D hD (hgood k hk)
        linarith)
  have hz:=mul_le_mul_of_nonneg_left (variance_le_envelope_zero p t (G 0) f)
    (pow_nonneg (show 0≤1-D*t by linarith) K)
  have he:=mul_le_mul_of_nonneg_right (pow_one_sub_lower (mul_nonneg hD ht) hDt K) (var_nonneg p f)
  have heq : -2*(K:ℝ)*(D*t)= -2*D*T := by rw [←hT]; ring
  rw [heq] at he
  rw [←hT]
  rw [←hT] at he
  nlinarith

theorem localization_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    b*(n:ℝ)*exp (-2*D*T)*var p f ≤
      b*(n:ℝ)*((D*T+L)*energy p f+16*(n:ℝ)^2*T*t*avg p (fun x => (f x)^2))+
      avg p (fun x => (f x)^2)*(exp (4*T/a)*(T*(W*(n:ℝ)+
        A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+64*(n:ℝ)^2*T*t)+1) := by
  have hv:=envelope_bound p hp f ht htn K G hG hprefix D T hD hDt hT hcov
  have hterm:=envelope_terminal_bound p hp f hf ht (G K) E (hG K) hE hGE L hL hterminal
  have hentropy:=entropy_bound p hp f hf ht htn K B hB W A a T hW hA ha hT hsmall hmean
  have he:=entropy_event_bound p (squarePrior p f hf) hp ht K E hE (b*(n:ℝ))
    (by simpa only [neg_mul] using hEsmall)
  have heN:=mul_le_mul_of_nonneg_left he hf.le
  have hvb:=mul_le_mul_of_nonneg_left hv (show 0≤b*(n:ℝ) by positivity)
  have htb:=mul_le_mul_of_nonneg_left hterm (show 0≤b*(n:ℝ) by positivity)
  have hHN:=mul_le_mul_of_nonneg_left hentropy hf.le
  nlinarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_CondSubConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open scoped BigOperators
noncomputable section
variable {n : ℕ}

lemma cond_sub_const (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) (c : ℝ)
    (i : Fin n) (x : Spin n) : cond p i (fun x => f x-c) x=cond p i f x-c := by
  unfold cond
  field_simp [(add_pos (hp x) (hp (flip i x))).ne']
  ring

lemma energy_sub_const (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) (c : ℝ) :
    energy p (fun x => f x-c)=energy p f := by
  unfold energy
  simp_rw [cond_sub_const p hp f c,sub_sub_sub_cancel_right]

lemma var_center (p : Prior n) (f : Spin n→ℝ) :
    var p (fun x => f x-avg p f)=var p f := by
  unfold var
  rw [avg_center]
  simp only [sub_zero]

end
end SKGap.GaussianStep

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma localization_scalar {den N E r c e s v w : ℝ} (hd : 0<den) (hN : 0<N)
    (H : den*r*N≤den*(c*E+e*N)+N*(s*(v+w*E/N)+1)) :
    (r-(e+(s*v+1)/den))*N≤(c+s*w/den)*E := by
  have he : den*((r-(e+(s*v+1)/den))*N-(c+s*w/den)*E)=
      den*r*N-(den*(c*E+e*N)+N*(s*(v+w*E/N)+1)) := by
    field_simp
    ring
  have hh : den*((r-(e+(s*v+1)/den))*N-(c+s*w/den)*E)≤0 := by
    rw [he]
    linarith
  have hz : (r-(e+(s*v+1)/den))*N-(c+s*w/den)*E ≤ 0 := by
    by_contra hz
    have hm := mul_pos hd (lt_of_not_ge hz)
    linarith
  linarith

lemma centered_localization_bound (p : Prior n) (hp : ∀x,0<p x) (hn : 0<n)
    (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2)) (hc : avg p f=0)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    (exp (-2*D*T)-localizationLoss n t W A a b T)*var p f≤
      localizationCost n A a b D L T*energy p f := by
  have hh:=localization_bound p hp f hf ht htn K B G hB hG E hE hprefix hGE
    D W A a b L T hD hW hA ha hb hL hDt hT hsmall hEsmall hmean hcov hterminal
  have hv : var p f=avg p (fun x => (f x)^2) := by rw [var_eq,hc]; ring
  rw [hv] at hh ⊢
  let v:=T*(W*(n:ℝ)+2*A*sqrt (n:ℝ)+4/a)+64*(n:ℝ)^2*T*t
  let w:=T*A*sqrt (n:ℝ)
  have hbody : T*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
      64*(n:ℝ)^2*T*t = v+w*energy p f/avg p (fun x => (f x)^2) := by dsimp [v,w]; ring
  rw [hbody] at hh
  simpa only [localizationLoss,localizationCost,v,w,mul_assoc] using
    localization_scalar (mul_pos hb (by exact_mod_cast hn)) hf hh

theorem poincare_of_history_estimates_s2_oai (p : Prior n) (hp : ∀x,0<p x) (hn : 0<n)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T C : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hC : 0≤C)
    (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀(f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2)),∀k<K,∀h:History n k,h∉B k →
      driftSquare p (squarePrior p f hf) t h ≤
        W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀(f : Spin n→ℝ),∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀(f : Spin n→ℝ),∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f)
    (hLoss : localizationLoss n t W A a b T≤exp (-2*D*T)/2)
    (hCost : localizationCost n A a b D L T≤C) :
    ∀f : Spin n→ℝ,var p f≤(2*C/exp (-2*D*T))*energy p f := by
  intro f
  by_cases hv : 0<var p f
  · let F:=fun x => f x-avg p f
    have hF : 0<avg p (fun x => (F x)^2) := hv
    have hh:=centered_localization_bound p hp hn F hF (avg_center p f) ht htn K B G hB hG E hE hprefix hGE
      D W A a b L T hD hW hA ha hb hL hDt hT hsmall hEsmall (hmean F hF) (hcov F) (hterminal F)
    dsimp [F] at hh
    rw [var_center,energy_sub_const p hp] at hh
    have hl:=mul_le_mul_of_nonneg_right hLoss hv.le
    have hc:=mul_le_mul_of_nonneg_right hCost (energy_nonneg p f)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (exp_pos (-2*D*T))).mpr
    nlinarith
  · have hz : var p f=0 := le_antisymm (le_of_not_gt hv) (var_nonneg p f)
    rw [hz]
    exact mul_nonneg (div_nonneg (by positivity) (exp_pos _).le) (energy_nonneg p f)

end
end SKGap.GaussianHistory

end OAI
end

theorem solution : type_of% @OAI.SKGap.GaussianHistory.poincare_of_history_estimates_s2_oai := @OAI.SKGap.GaussianHistory.poincare_of_history_estimates_s2_oai
