-- Prove2me | solution 1 for OAI.CriticalSK.critical_two_clock_mixing_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:02:47.805417+00:00
-- url     : https://prove2.me/submissions/3005fb97-b775-4cec-8018-fe78996e4f85

import Mathlib
import Definitions.Def_CriticalSKMixing
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ074C000
import Theorems.Thm_OAI_SKGap_sk_main
import Theorems.Thm_OAI_CriticalSK_natural_smallBallObstruction_probability_s2

section
-- module Solutions.OAIQ074_CM.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

lemma gaussian_exp_integrable (v : ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z => Real.exp (gaussianLinear a z)) (gaussianScalarPi v) := by
  simp only [gaussianLinear,Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

lemma gaussian_exp_integral (v : ℝ≥0) (a : ι → ℝ) :
    (∫ z, Real.exp (gaussianLinear a z) ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*(∑ i, a i^2)/2) := by
  simp only [gaussianLinear,Real.exp_sum,gaussianScalarPi]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => gaussianReal 0 v) (fun i (z : ℝ) => Real.exp (a i*z))]
  have he (i : ι) : (∫ z : ℝ, Real.exp (a i*z) ∂gaussianReal 0 v) = Real.exp ((v:ℝ)*(a i)^2/2) := by
    have hh := mgf_gaussianReal (p := gaussianReal 0 v) (X := id) (μ := 0) (v := v) (by simp) (a i)
    simpa only [mgf,zero_mul,zero_add,id_eq] using hh
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_div]

end

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Gibbs
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

section FiniteGibbs

variable {n : ℕ} (W : Disorder n)

lemma gibbs_sum : ∑ x : Spin n, gibbs W x = 1 := by
  unfold gibbs
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos W))

lemma sameExcept_refl (i : Fin n) (x : Spin n) : sameExcept i x x := by
  intro _ _
  rfl

lemma fiberMass_pos (i : Fin n) (x : Spin n) : 0 < fiberMass W i x := by
  have h : gibbs W x ≤ fiberMass W i x := by
    unfold fiberMass
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun z => if sameExcept i x z then gibbs W z else 0)
      (fun z _ => by split_ifs; exact gibbs_nonneg W z; exact le_rfl) (Finset.mem_univ x)
    simpa only [sameExcept_refl, ite_true] using hh
  exact lt_of_lt_of_le (gibbs_pos W x) h

lemma siteKernel_nonneg (i : Fin n) (x y : Spin n) : 0 ≤ siteKernel W i x y := by
  unfold siteKernel
  split_ifs
  · exact (div_pos (gibbs_pos W y) (fiberMass_pos W i x)).le
  · exact le_rfl

lemma siteKernel_sum (i : Fin n) (x : Spin n) : ∑ y, siteKernel W i x y = 1 := by
  calc
    (∑ y, siteKernel W i x y) = fiberMass W i x / fiberMass W i x := by
      unfold siteKernel fiberMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = 1 := div_self (ne_of_gt (fiberMass_pos W i x))

lemma siteKernel_same_row {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    siteKernel W i x = siteKernel W i y := by
  funext z
  change (if sameExcept i x z then gibbs W z / fiberMass W i x else 0) =
    (if sameExcept i y z then gibbs W z / fiberMass W i y else 0)
  simp only [sameExcept_classes h z, fiberMass_eq W h]

lemma siteKernel_projection (i : Fin n) : siteKernel W i * siteKernel W i = siteKernel W i := by
  ext x z
  change (∑ y, siteKernel W i x y * siteKernel W i y z) = siteKernel W i x z
  calc
    (∑ y, siteKernel W i x y * siteKernel W i y z) =
        ∑ y, siteKernel W i x y * siteKernel W i x z := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : sameExcept i x y
      · rw [siteKernel_same_row W h]
      · simp [siteKernel, h]
    _ = siteKernel W i x z := by rw [← Finset.sum_mul, siteKernel_sum, one_mul]

end FiniteGibbs

variable {n : ℕ} (W : Disorder n)

lemma mean_nonneg {f : Spin n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean W f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (gibbs_nonneg W x) (hf x))

lemma mean_mono {f g : Spin n → ℝ} (h : ∀ x, f x ≤ g x) : mean W f ≤ mean W g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (gibbs_nonneg W x))

@[simp] lemma mean_const (c : ℝ) : mean W (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, gibbs_sum, one_mul]

lemma mean_add (f g : Spin n → ℝ) :
    mean W (fun x => f x + g x) = mean W f + mean W g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (f g : Spin n → ℝ) :
    mean W (fun x => f x - g x) = mean W f - mean W g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_neg (f : Spin n → ℝ) : mean W (fun x => -f x) = -mean W f := by
  simp only [mean, mul_neg, Finset.sum_neg_distrib]

lemma mean_mul_const (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => f x * c) = mean W f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

lemma mean_const_mul (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => c * f x) = c * mean W f := by
  simpa only [mul_comm c] using mean_mul_const W f c

lemma mean_sum {ι : Type*} (s : Finset ι) (f : ι → Spin n → ℝ) :
    mean W (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, mean W (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

lemma siteAverage_eq (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    siteAverage W i f x = ∑ y, siteKernel W i x y * f y := rfl

lemma siteAverage_sub (i : Fin n) (f g : Spin n → ℝ) :
    siteAverage W i (fun x => f x - g x) =
      fun x => siteAverage W i f x - siteAverage W i g x := by
  funext x
  simp only [siteAverage_eq, mul_sub, Finset.sum_sub_distrib]

lemma siteAverage_idempotent (i : Fin n) (f : Spin n → ℝ) :
    siteAverage W i (siteAverage W i f) = siteAverage W i f := by
  unfold siteAverage
  rw [Matrix.mulVec_mulVec, siteKernel_projection]

lemma siteAverage_fiber_constant (i : Fin n) (f : Spin n → ℝ)
    {x y : Spin n} (h : sameExcept i x y) :
    siteAverage W i f x = siteAverage W i f y := by
  simp only [siteAverage_eq, siteKernel_same_row W h]

lemma siteAverage_of_fiber_constant (i : Fin n) (f : Spin n → ℝ)
    (hf : ∀ x y, sameExcept i x y → f y = f x) : siteAverage W i f = f := by
  funext x
  calc
    siteAverage W i f x = ∑ y, siteKernel W i x y * f x := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : sameExcept i x y
      · rw [hf x y h]
      · simp [siteKernel, h]
    _ = f x := by rw [← Finset.sum_mul, siteKernel_sum, one_mul]

lemma siteAverage_selfadjoint (i : Fin n) (f g : Spin n → ℝ) :
    mean W (fun x => f x * siteAverage W i g x) =
      mean W (fun x => siteAverage W i f x * g x) := by
  simp only [mean, siteAverage_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    gibbs W y * (f y * (siteKernel W i y x * g x)) =
      (gibbs W y * siteKernel W i y x) * (f y * g x) := by ring
    _ = (gibbs W x * siteKernel W i x y) * (f y * g x) := by
      rw [siteKernel_reversible]
    _ = gibbs W x * (siteKernel W i x y * f y * g x) := by ring

lemma siteAverage_orthogonal (i : Fin n) (f g : Spin n → ℝ)
    (hg : siteAverage W i g = g) :
    mean W (fun x => (f x - siteAverage W i f x) * g x) = 0 := by
  have h := siteAverage_selfadjoint W i f g
  rw [hg] at h
  simp only [sub_mul, mean_sub]
  exact sub_eq_zero.mpr h

theorem siteAverage_least_squares (i : Fin n) (f g : Spin n → ℝ)
    (hg : ∀ x y, sameExcept i x y → g y = g x) :
    mean W (fun x => (f x - siteAverage W i f x) ^ 2) ≤
      mean W (fun x => (f x - g x) ^ 2) := by
  have hfixed : siteAverage W i (fun x => siteAverage W i f x - g x) =
      (fun x => siteAverage W i f x - g x) := by
    rw [siteAverage_sub, siteAverage_idempotent, siteAverage_of_fiber_constant W i g hg]
  have horth := siteAverage_orthogonal W i f _ hfixed
  have hexpand : mean W (fun x => (f x - g x) ^ 2) =
      mean W (fun x => (f x - siteAverage W i f x) ^ 2) +
      mean W (fun x => (siteAverage W i f x - g x) ^ 2) +
      2 * mean W (fun x => (f x - siteAverage W i f x) * (siteAverage W i f x - g x)) := by
    rw [← mean_const_mul, ← mean_add, ← mean_add]
    congr 1
    funext x
    ring
  rw [horth, mul_zero, add_zero] at hexpand
  have hnonneg := mean_nonneg W (fun x => sq_nonneg (siteAverage W i f x - g x))
  linarith

lemma siteAverage_form_identity (i : Fin n) (f : Spin n → ℝ) :
    mean W (fun x => (f x - siteAverage W i f x) ^ 2) =
      mean W (fun x => f x * (f x - siteAverage W i f x)) := by
  have hfixed := siteAverage_idempotent W i f
  have horth := siteAverage_orthogonal W i f _ hfixed
  have hexpand : mean W (fun x => f x * (f x - siteAverage W i f x)) =
      mean W (fun x => (f x - siteAverage W i f x) ^ 2) +
      mean W (fun x => (f x - siteAverage W i f x) * siteAverage W i f x) := by
    rw [← mean_add]
    congr 1
    funext x
    ring
  linarith

lemma dirichlet_nonneg (f : Spin n → ℝ) : 0 ≤ dirichlet W f := by
  apply Finset.sum_nonneg
  intro i _
  exact mean_nonneg W (fun _ => sq_nonneg _)

lemma dirichlet_generator (f : Spin n → ℝ) :
    dirichlet W f = -mean W (fun x => f x * (generator W).mulVec f x) := by
  have hgen : (generator W).mulVec f = fun x =>
      ∑ i : Fin n, (siteAverage W i f x - f x) := by
    ext x
    simp [generator, Matrix.sum_mulVec, Matrix.sub_mulVec, siteAverage]
  rw [hgen]
  unfold dirichlet
  simp_rw [← siteAverage_eq, siteAverage_form_identity]
  rw [show (fun x => f x * ∑ i : Fin n, (siteAverage W i f x - f x)) =
      (fun x => ∑ i : Fin n, -(f x * (f x - siteAverage W i f x))) by
    funext x; simp only [Finset.mul_sum]; congr 1; funext i; ring]
  simp only [mean_sum, mean_neg, Finset.sum_neg_distrib, neg_neg]

lemma linearObservable_split (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    linearObservable a x = a i * spinValue (x i) + linearRest a i x := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

lemma linearRest_fiber_constant (a : Fin n → ℝ) (i : Fin n) (x y : Spin n)
    (h : sameExcept i x y) : linearRest a i y = linearRest a i x := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.ne_of_mem_erase hj)]

theorem dirichlet_linear_le (a : Fin n → ℝ) :
    dirichlet W (linearObservable a) ≤ ∑ i : Fin n, a i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  calc
    mean W (fun x => (linearObservable a x - ∑ y, siteKernel W i x y * linearObservable a y) ^ 2)
        ≤ mean W (fun x => (linearObservable a x - linearRest a i x) ^ 2) :=
      siteAverage_least_squares W i _ _ (linearRest_fiber_constant a i)
    _ = a i ^ 2 := by
      simp_rw [linearObservable_split a i, add_sub_cancel_right, mul_pow, spinValue_sq, mul_one]
      exact mean_const W _

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_HeatBath
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

open scoped InnerProductSpace

section GibbsEuclidean

variable {n : ℕ} (W : Disorder n)

lemma gibbsEuclideanEquiv_inner (f g : Spin n → ℝ) :
    ⟪gibbsEuclideanEquiv W f, gibbsEuclideanEquiv W g⟫_ℝ =
      mean W (fun x => f x * g x) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp only [RCLike.inner_apply, conj_trivial, gibbsEuclideanEquiv_apply]
  calc
    (Real.sqrt (gibbs W x) * g x) * (Real.sqrt (gibbs W x) * f x) =
        (Real.sqrt (gibbs W x)) ^ 2 * (f x * g x) := by ring
    _ = gibbs W x * (f x * g x) := by rw [Real.sq_sqrt (gibbs_nonneg W x)]

lemma kernelConjugate_apply (K : Matrix (Spin n) (Spin n) ℝ) (f : Spin n → ℝ) :
    (kernelConjugate W K).toEuclideanLin (gibbsEuclideanEquiv W f) =
      gibbsEuclideanEquiv W (K.mulVec f) := by
  ext x
  change (∑ y, (Real.sqrt (gibbs W x) * K x y / Real.sqrt (gibbs W y)) *
    (Real.sqrt (gibbs W y) * f y)) = Real.sqrt (gibbs W x) * ∑ y, K x y * f y
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [ne_of_gt (gibbs_sqrt_pos W y)]

lemma discreteKernel_nonneg (x y : Spin n) : 0 ≤ discreteKernel W x y := by
  simp only [discreteKernel, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  change 0 ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, siteKernel W i x y
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_nonneg (fun i _ => siteKernel_nonneg W i x y)

lemma discreteKernel_sum (hn : 0 < n) (x : Spin n) : ∑ y, discreteKernel W x y = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp only [discreteKernel, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  change (∑ y, (n : ℝ)⁻¹ * ∑ i : Fin n, siteKernel W i x y) = 1
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp [siteKernel_sum, hn0]

lemma discreteKernel_stationary (hn : 0 < n) (y : Spin n) :
    ∑ x, gibbs W x * discreteKernel W x y = gibbs W y := by
  simp_rw [discreteKernel_reversible]
  rw [← Finset.mul_sum, discreteKernel_sum W hn, mul_one]

lemma discreteKernel_average (f : Spin n → ℝ) (x : Spin n) :
    (discreteKernel W).mulVec f x = (n : ℝ)⁻¹ * ∑ i : Fin n, siteAverage W i f x := by
  simp only [discreteKernel, Matrix.smul_mulVec, Matrix.sum_mulVec, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, siteAverage]

lemma siteAverage_self_square (i : Fin n) (f : Spin n → ℝ) :
    mean W (fun x => f x * siteAverage W i f x) =
      mean W (fun x => (siteAverage W i f x) ^ 2) := by
  have h := siteAverage_selfadjoint W i f (siteAverage W i f)
  simpa only [siteAverage_idempotent, sq] using h

lemma discreteKernel_quadratic_nonneg (f : Spin n → ℝ) :
    0 ≤ mean W (fun x => f x * (discreteKernel W).mulVec f x) := by
  have heq : mean W (fun x => f x * (discreteKernel W).mulVec f x) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, mean W (fun x => (siteAverage W i f x) ^ 2) := by
    simp_rw [discreteKernel_average, mul_left_comm (f _), Finset.mul_sum,
      mean_sum, mean_const_mul, siteAverage_self_square]
  rw [heq]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_nonneg (fun _ _ => mean_nonneg W (fun _ => sq_nonneg _))

lemma generator_discreteKernel (hn : 0 < n) :
    generator W = (n : ℝ) • (discreteKernel W - 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp [generator, discreteKernel, smul_sub, smul_smul, hn0, Finset.sum_sub_distrib]
  simp [Nat.cast_smul_eq_nsmul]

lemma dirichlet_discrete (hn : 0 < n) (f : Spin n → ℝ) :
    mean W (fun x => f x * (f x - (discreteKernel W).mulVec f x)) =
      dirichlet W f / n := by
  rw [dirichlet_generator, generator_discreteKernel W hn,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hfunc : (fun x => f x * ((n : ℝ) * ((discreteKernel W).mulVec f x - f x))) =
      (fun x => -(n : ℝ) * (f x * (f x - (discreteKernel W).mulVec f x))) := by
    funext x
    ring
  rw [hfunc, mean_const_mul]
  field_simp

end GibbsEuclidean

section HermitianIncrements

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {A : Matrix ι ι ℝ} (hA : A.IsHermitian)

lemma hermitian_eigenbasis_apply (i : ι) :
    A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  ext j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

lemma hermitian_repr_apply (v : EuclideanSpace ℝ ι) (i : ι) :
    hA.eigenvectorBasis.repr (A.toEuclideanLin v) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr v i := by
  rw [OrthonormalBasis.repr_apply_apply, ← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (hA.eigenvectorBasis i) v, hermitian_eigenbasis_apply hA,
    real_inner_smul_left, OrthonormalBasis.repr_apply_apply]

lemma hermitian_repr_pow (k : ℕ) (v : EuclideanSpace ℝ ι) (i : ι) :
    hA.eigenvectorBasis.repr ((A ^ k).toEuclideanLin v) i =
      hA.eigenvalues i ^ k * hA.eigenvectorBasis.repr v i := by
  induction k with
  | zero => simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  | succ k ih =>
    rw [pow_succ', Matrix.toEuclideanLin, Matrix.toLpLin_mul]
    change hA.eigenvectorBasis.repr (A.toEuclideanLin ((A ^ k).toEuclideanLin v)) i = _
    rw [hermitian_repr_apply hA, ih, pow_succ']
    ring

lemma hermitian_inner_sub_pow (k : ℕ) (v : EuclideanSpace ℝ ι) :
    ⟪v, v - (A ^ k).toEuclideanLin v⟫_ℝ =
      ∑ i, (hA.eigenvectorBasis.repr v i) ^ 2 * (1 - hA.eigenvalues i ^ k) := by
  rw [← hA.eigenvectorBasis.repr.inner_map_map, map_sub, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.sub_apply, RCLike.inner_apply, conj_trivial,
    hermitian_repr_pow hA]
  ring

lemma one_sub_pow_le_mul (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k : ℕ) :
    1 - θ ^ k ≤ (k : ℝ) * (1 - θ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : θ ^ k ≤ 1 := pow_le_one₀ hθ0 hθ1
    have ht : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    rw [pow_succ, Nat.cast_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) ht]

lemma hermitian_power_increment_le (hθ : ∀ i, hA.eigenvalues i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (v : EuclideanSpace ℝ ι) :
    ⟪v, v - (A ^ k).toEuclideanLin v⟫_ℝ ≤
      (k : ℝ) * ⟪v, v - A.toEuclideanLin v⟫_ℝ := by
  rw [hermitian_inner_sub_pow hA]
  conv_rhs => rw [← pow_one A, hermitian_inner_sub_pow hA]
  simp only [pow_one]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (one_sub_pow_le_mul (hA.eigenvalues i) (hθ i).1 (hθ i).2 k)
    (sq_nonneg (hA.eigenvectorBasis.repr v i))
  nlinarith only [h]

end HermitianIncrements

section DiscreteIncrements

variable {n : ℕ} (W : Disorder n)

lemma kernelConjugate_pow_apply (K : Matrix (Spin n) (Spin n) ℝ)
    (k : ℕ) (f : Spin n → ℝ) :
    (kernelConjugate W K ^ k).toEuclideanLin (gibbsEuclideanEquiv W f) =
      gibbsEuclideanEquiv W ((K ^ k).mulVec f) := by
  induction k with
  | zero => simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  | succ k ih =>
    rw [pow_succ', Matrix.toEuclideanLin, Matrix.toLpLin_mul]
    change (kernelConjugate W K).toEuclideanLin
      ((kernelConjugate W K ^ k).toEuclideanLin (gibbsEuclideanEquiv W f)) = _
    rw [ih, kernelConjugate_apply, pow_succ', ← Matrix.mulVec_mulVec]

lemma discreteKernel_eigenvalues (hn : 0 < n) (i : Spin n) :
    (kernelConjugate_isHermitian W (discreteKernel W)
      (discreteKernel_reversible W)).eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  let hA := kernelConjugate_isHermitian W (discreteKernel W) (discreteKernel_reversible W)
  let v := hA.eigenvectorBasis i
  let f := (gibbsEuclideanEquiv W).symm v
  have hf : gibbsEuclideanEquiv W f = v := (gibbsEuclideanEquiv W).apply_symm_apply v
  have hnorm : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hA.eigenvectorBasis.orthonormal.norm_eq_one]
    norm_num
  have heig := hermitian_eigenbasis_apply hA i
  change (kernelConjugate W (discreteKernel W)).toEuclideanLin v =
    hA.eigenvalues i • v at heig
  have hpos := discreteKernel_quadratic_nonneg W f
  rw [← gibbsEuclideanEquiv_inner, ← kernelConjugate_apply, hf, heig,
    inner_smul_right, hnorm, mul_one] at hpos
  have hneg : 0 ≤ ⟪v, v - (kernelConjugate W (discreteKernel W)).toEuclideanLin v⟫_ℝ := by
    rw [← hf, kernelConjugate_apply, ← map_sub, gibbsEuclideanEquiv_inner]
    change 0 ≤ mean W (fun x => f x * (f x - (discreteKernel W).mulVec f x))
    rw [dirichlet_discrete W hn]
    exact div_nonneg (dirichlet_nonneg W f) (Nat.cast_nonneg n)
  rw [heig, inner_sub_right, inner_smul_right, hnorm, mul_one] at hneg
  exact ⟨hpos, by linarith⟩

theorem discrete_inner_increment_le (hn : 0 < n) (k : ℕ) (f : Spin n → ℝ) :
    mean W (fun x => f x * (f x - (discreteKernel W ^ k).mulVec f x)) ≤
      (k : ℝ) / n * dirichlet W f := by
  have h := hermitian_power_increment_le
    (kernelConjugate_isHermitian W (discreteKernel W) (discreteKernel_reversible W))
    (discreteKernel_eigenvalues W hn) k (gibbsEuclideanEquiv W f)
  rw [kernelConjugate_pow_apply, kernelConjugate_apply,
    ← map_sub, ← map_sub, gibbsEuclideanEquiv_inner, gibbsEuclideanEquiv_inner] at h
  change mean W (fun x => f x * (f x - (discreteKernel W ^ k).mulVec f x)) ≤
    (k : ℝ) * mean W (fun x => f x * (f x - (discreteKernel W).mulVec f x)) at h
  rw [dirichlet_discrete W hn] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end DiscreteIncrements

section FiniteKernels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma kernel_mul_nonneg {K L : Matrix ι ι ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hL : ∀ x y, 0 ≤ L x y) (x y : ι) :
    0 ≤ (K * L) x y :=
  Finset.sum_nonneg fun z _ => mul_nonneg (hK x z) (hL z y)

omit [DecidableEq ι] in
lemma kernel_mul_sum {K L : Matrix ι ι ℝ}
    (hK : ∀ x, ∑ y, K x y = 1) (hL : ∀ x, ∑ y, L x y = 1) (x : ι) :
    ∑ y, (K * L) x y = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hL, mul_one]
  exact hK x

omit [DecidableEq ι] in
lemma kernel_mul_stationary {K L : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hK : ∀ y, ∑ x, μ x * K x y = μ y)
    (hL : ∀ y, ∑ x, μ x * L x y = μ y) (y : ι) :
    ∑ x, μ x * (K * L) x y = μ y := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hK]
  exact hL y

lemma kernel_pow_nonneg {K : Matrix ι ι ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (k : ℕ) (x y : ι) : 0 ≤ (K ^ k) x y := by
  induction k generalizing x y with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih => rw [pow_succ]; exact kernel_mul_nonneg ih hK x y

lemma kernel_pow_sum {K : Matrix ι ι ℝ}
    (hK : ∀ x, ∑ y, K x y = 1) (k : ℕ) (x : ι) : ∑ y, (K ^ k) x y = 1 := by
  induction k generalizing x with
  | zero => simp [Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact kernel_mul_sum ih hK x

lemma kernel_pow_stationary {K : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hK : ∀ y, ∑ x, μ x * K x y = μ y) (k : ℕ) (y : ι) :
    ∑ x, μ x * (K ^ k) x y = μ y := by
  induction k generalizing y with
  | zero => simp [Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact kernel_mul_stationary ih hK y

omit [DecidableEq ι] in
lemma stationary_increment_identity {K : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hstationary : ∀ y, ∑ x, μ x * K x y = μ y) (f : ι → ℝ) :
    (∑ x, ∑ y, μ x * K x y * (f y - f x) ^ 2) =
      2 * ∑ x, μ x * (f x * (f x - K.mulVec f x)) := by
  have hsquare : (∑ x, ∑ y, μ x * K x y * (f y) ^ 2) = ∑ y, μ y * (f y) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hstationary]
  have hstart : (∑ x, ∑ y, μ x * K x y * (f x) ^ 2) = ∑ x, μ x * (f x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = μ x * (f x) ^ 2 * ∑ y, K x y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = μ x * (f x) ^ 2 := by rw [hrow, mul_one]
  have hexpand : (∑ x, ∑ y, μ x * K x y * (f y - f x) ^ 2) =
      (∑ x, ∑ y, μ x * K x y * (f y) ^ 2) +
      (∑ x, ∑ y, μ x * K x y * (f x) ^ 2) -
      2 * ∑ x, μ x * f x * K.mulVec f x := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hexpand, hsquare, hstart]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteKernels

section StationaryIncrements

variable {n : ℕ} (W : Disorder n)

theorem stationary_increment_discrete (hn : 0 < n) (k : ℕ) (f : Spin n → ℝ) :
    (∑ x, ∑ y, gibbs W x * (discreteKernel W ^ k) x y * (f y - f x) ^ 2) ≤
      (2 * k : ℝ) / n * dirichlet W f := by
  rw [stationary_increment_identity (kernel_pow_sum (discreteKernel_sum W hn) k)
    (kernel_pow_stationary (discreteKernel_stationary W hn) k)]
  calc
    2 * mean W (fun x => f x * (f x - (discreteKernel W ^ k).mulVec f x)) ≤
        2 * ((k : ℝ) / n * dirichlet W f) :=
      mul_le_mul_of_nonneg_left (discrete_inner_increment_le W hn k f) (by norm_num)
    _ = _ := by ring

end StationaryIncrements

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator in

lemma matrix_exp_hasSum (A : Matrix ι ι ℝ) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A ^ k) (NormedSpace.exp A) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A

lemma matrix_exp_entry_hasSum (A : Matrix ι ι ℝ) (x y : ι) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * (A ^ k) x y) (NormedSpace.exp A x y) := by
  exact ((Pi.hasSum.mp (Pi.hasSum.mp (matrix_exp_hasSum A) x)) y)

lemma matrix_exp_scalar (a : ℝ) :
    NormedSpace.exp (a • (1 : Matrix ι ι ℝ)) = Real.exp a • (1 : Matrix ι ι ℝ) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext x y
  simp [Matrix.diagonal_apply, Matrix.one_apply, Pi.coe_exp, ← Real.exp_eq_exp_ℝ]

lemma matrix_poisson_exp (P : Matrix ι ι ℝ) (a : ℝ) :
    NormedSpace.exp (a • (P - 1)) = Real.exp (-a) • NormedSpace.exp (a • P) := by
  have hcomm : Commute ((-a) • (1 : Matrix ι ι ℝ)) (a • P) := by
    exact (Commute.one_left P).smul_left (-a) |>.smul_right a
  have hsplit : a • (P - 1) = (-a) • (1 : Matrix ι ι ℝ) + a • P := by
    simp [neg_smul, sub_eq_add_neg, add_comm]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, matrix_exp_scalar]
  simp

lemma matrix_poisson_hasSum (P : Matrix ι ι ℝ) (a : ℝ) (x y : ι) :
    HasSum (fun k : ℕ => (Real.exp (-a) * a ^ k / k.factorial) * (P ^ k) x y)
      (NormedSpace.exp (a • (P - 1)) x y) := by
  have h := (matrix_exp_entry_hasSum (a • P) x y).mul_left (Real.exp (-a))
  rw [matrix_poisson_exp]
  change HasSum _ (Real.exp (-a) * NormedSpace.exp (a • P) x y)
  apply h.congr_fun
  intro k
  simp only [_root_.smul_pow, Matrix.smul_apply, smul_eq_mul]
  ring

lemma poisson_coeff_hasSum (a : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-a) * a ^ k / k.factorial) 1 := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  apply h.congr_fun
  intro k
  simp only [smul_eq_mul]
  ring

lemma poisson_coeff_moment_hasSum (a : ℝ) :
    HasSum (fun k : ℕ => (Real.exp (-a) * a ^ k / k.factorial) * k) a := by
  have h := (poisson_coeff_hasSum a).mul_left a
  rw [mul_one] at h
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_zero,
    mul_zero, sub_zero]
  apply h.congr_fun
  intro k
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma poisson_coeff_nonneg (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    0 ≤ Real.exp (-a) * a ^ k / k.factorial := by positivity

end

section PoissonKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma poisson_kernel_nonneg {P : Matrix ι ι ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (a : ℝ) (ha : 0 ≤ a) (x y : ι) :
    0 ≤ NormedSpace.exp (a • (P - 1)) x y := by
  apply HasSum.nonneg _ (matrix_poisson_hasSum P a x y)
  intro k
  exact mul_nonneg (poisson_coeff_nonneg a ha k) (kernel_pow_nonneg hP k x y)

lemma poisson_kernel_sum {P : Matrix ι ι ℝ} (hP : ∀ x, ∑ y, P x y = 1)
    (a : ℝ) (x : ι) : ∑ y, NormedSpace.exp (a • (P - 1)) x y = 1 := by
  have h := hasSum_sum (s := Finset.univ) (fun y _ => matrix_poisson_hasSum P a x y)
  simp_rw [← Finset.mul_sum, kernel_pow_sum hP, mul_one] at h
  exact h.unique (poisson_coeff_hasSum a)

lemma poisson_kernel_stationary {P : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hP : ∀ y, ∑ x, μ x * P x y = μ y) (a : ℝ) (y : ι) :
    ∑ x, μ x * NormedSpace.exp (a • (P - 1)) x y = μ y := by
  have h := hasSum_sum (s := Finset.univ) (fun x _ =>
    (matrix_poisson_hasSum P a x y).mul_left (μ x))
  simp_rw [mul_left_comm (μ _), ← Finset.mul_sum, kernel_pow_stationary hP] at h
  have h' := (poisson_coeff_hasSum a).mul_right (μ y)
  rw [one_mul] at h'
  exact h.unique h'

lemma poisson_stationary_increment_le {P : Matrix ι ι ℝ} {μ : ι → ℝ}
    (f : ι → ℝ) (D : ℝ)
    (hincrement : ∀ k : ℕ, (∑ x, ∑ y, μ x * (P ^ k) x y * (f y - f x) ^ 2) ≤ (k : ℝ) * D)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ x, ∑ y, μ x * NormedSpace.exp (a • (P - 1)) x y * (f y - f x) ^ 2) ≤ a * D := by
  have h := hasSum_sum (s := Finset.univ) (fun x _ =>
    hasSum_sum (s := Finset.univ) (fun y _ =>
      ((matrix_poisson_hasSum P a x y).mul_left (μ x)).mul_right ((f y - f x) ^ 2)))
  have hleft : HasSum (fun k : ℕ => (Real.exp (-a) * a ^ k / k.factorial) *
      (∑ x, ∑ y, μ x * (P ^ k) x y * (f y - f x) ^ 2))
      (∑ x, ∑ y, μ x * NormedSpace.exp (a • (P - 1)) x y * (f y - f x) ^ 2) := by
    apply h.congr_fun
    intro k
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hright := (poisson_coeff_moment_hasSum a).mul_right D
  apply hasSum_le _ hleft hright
  intro k
  calc
    _ ≤ (Real.exp (-a) * a ^ k / k.factorial) * ((k : ℝ) * D) :=
      mul_le_mul_of_nonneg_left (hincrement k) (poisson_coeff_nonneg a ha k)
    _ = _ := by ring

end PoissonKernel

section ContinuousIncrements

variable {n : ℕ} (W : Disorder n)

lemma continuousKernel_poisson (hn : 0 < n) (t : ℝ) :
    continuousKernel W t = NormedSpace.exp (((n : ℝ) * t) • (discreteKernel W - 1)) := by
  rw [continuousKernel, generator_discreteKernel W hn, smul_smul, mul_comm]

lemma continuousKernel_nonneg (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) (x y : Spin n) :
    0 ≤ continuousKernel W t x y := by
  rw [continuousKernel_poisson W hn]
  exact poisson_kernel_nonneg (discreteKernel_nonneg W) _
    (mul_nonneg (Nat.cast_nonneg n) ht) x y

lemma continuousKernel_sum (hn : 0 < n) (t : ℝ) (x : Spin n) :
    ∑ y, continuousKernel W t x y = 1 := by
  rw [continuousKernel_poisson W hn]
  exact poisson_kernel_sum (discreteKernel_sum W hn) _ x

lemma continuousKernel_stationary (hn : 0 < n) (t : ℝ) (y : Spin n) :
    ∑ x, gibbs W x * continuousKernel W t x y = gibbs W y := by
  rw [continuousKernel_poisson W hn]
  exact poisson_kernel_stationary (discreteKernel_stationary W hn) _ y

theorem stationary_increment_continuous (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∑ x, ∑ y, gibbs W x * continuousKernel W t x y * (f y - f x) ^ 2) ≤
      2 * t * dirichlet W f := by
  rw [continuousKernel_poisson W hn]
  have hdt : ∀ k : ℕ, (∑ x, ∑ y, gibbs W x * (discreteKernel W ^ k) x y * (f y - f x) ^ 2) ≤
      (k : ℝ) * (2 * dirichlet W f / n) := by
    intro k
    calc
      _ ≤ (2 * k : ℝ) / n * dirichlet W f := stationary_increment_discrete W hn k f
      _ = _ := by ring
  have h := poisson_stationary_increment_le f (2 * dirichlet W f / n) hdt
    ((n : ℝ) * t) (mul_nonneg (Nat.cast_nonneg n) ht)
  calc
    _ ≤ ((n : ℝ) * t) * (2 * dirichlet W f / n) := h
    _ = 2 * t * dirichlet W f := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      field_simp

end ContinuousIncrements

section SignTest

variable {ι : Type*} [Fintype ι]

lemma finite_event_test {p μ : ι → ℝ} (hmass : ∑ y, p y = ∑ y, μ y)
    (s : ι → Prop) [DecidablePred s] :
    (∑ y, if s y then p y else 0) - (∑ y, if s y then μ y else 0) ≤
      (1 / 2 : ℝ) * ∑ y, |p y - μ y| := by
  let d : ι → ℝ := fun y => p y - μ y
  have hzero : ∑ y, d y = 0 := by simp [d, Finset.sum_sub_distrib, hmass]
  have hwhole : (∑ y, if s y then d y else 0) + (∑ y, if s y then 0 else d y) = 0 := by
    rw [← Finset.sum_add_distrib]
    simpa only [ite_add_ite, add_zero, zero_add, ite_self] using hzero
  have hineq : (∑ y, if s y then d y else 0) - (∑ y, if s y then 0 else d y) ≤
      ∑ y, |d y| := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : s y
    · simp only [hy, ite_true, sub_zero]; exact le_abs_self _
    · simp only [hy, ite_false, zero_sub]; exact neg_le_abs _
  have heq : (∑ y, if s y then p y else 0) - (∑ y, if s y then μ y else 0) =
      ∑ y, if s y then d y else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : s y <;> simp [hy, d]
  rw [heq]
  change _ ≤ (1 / 2 : ℝ) * ∑ y, |d y|
  linarith

lemma odd_halfspace_mass_le {μ : ι → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμsum : ∑ x, μ x = 1)
    (flip : Equiv.Perm ι) (hflip : ∀ x, μ (flip x) = μ x)
    (f : ι → ℝ) (hodd : ∀ x, f (flip x) = -f x) (c : ℝ) :
    (∑ y, if 0 < c * f y then μ y else 0) ≤ (1 / 2 : ℝ) := by
  have heq : (∑ y, if 0 < c * f y then μ y else 0) =
      ∑ y, if c * f y < 0 then μ y else 0 := by
    calc
      _ = ∑ y, if 0 < c * f (flip y) then μ (flip y) else 0 :=
        (Equiv.sum_comp flip _).symm
      _ = _ := by simp [hodd, hflip]
  have hdisjoint : (∑ y, if 0 < c * f y then μ y else 0) +
      (∑ y, if c * f y < 0 then μ y else 0) ≤ 1 := by
    rw [← hμsum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    by_cases hp : 0 < c * f y
    · simp [hp, not_lt.mpr hp.le]
    · by_cases hn : c * f y < 0
      · simp [hp, hn]
      · simp [hp, hn, hμ y]
  linarith

lemma sign_row_test {p μ : ι → ℝ} (hpsum : ∑ y, p y = 1) (hμsum : ∑ y, μ y = 1)
    (f : ι → ℝ) (c : ℝ)
    (hhalf : (∑ y, if 0 < c * f y then μ y else 0) ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) - (1 / 2 : ℝ) * ∑ y, |p y - μ y| ≤
      ∑ y, if c * f y ≤ 0 then p y else 0 := by
  have htv := finite_event_test (hpsum.trans hμsum.symm) (fun y => 0 < c * f y)
  have hcover : (∑ y, if 0 < c * f y then p y else 0) +
      (∑ y, if c * f y ≤ 0 then p y else 0) = 1 := by
    rw [← hpsum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : 0 < c * f y <;> simp [hy, le_of_not_gt, not_le.mpr]
  linarith

lemma sign_failure_pointwise (u v a : ℝ) (ha : 0 < a) :
    (if u * v ≤ 0 then (1 : ℝ) else 0) ≤
      (if |u| ≤ a then (1 : ℝ) else 0) + (v - u) ^ 2 / a ^ 2 := by
  have hnonneg : 0 ≤ (v - u) ^ 2 / a ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hsmall : |u| ≤ a
  · simp only [hsmall, ite_true]
    split_ifs <;> linarith
  · simp only [hsmall, ite_false, zero_add]
    split_ifs with hsign
    · have habs : a < |u| := lt_of_not_ge hsmall
      have hs : a ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs u]
      apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
      nlinarith [sq_nonneg v]
    · exact hnonneg

lemma sign_failure_average {μ : ι → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    {K : Matrix ι ι ℝ} (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1)
    (f : ι → ℝ) (a : ℝ) (ha : 0 < a) :
    (∑ x, μ x * ∑ y, if f x * f y ≤ 0 then K x y else 0) ≤
      (∑ x, if |f x| ≤ a then μ x else 0) +
      (∑ x, ∑ y, μ x * K x y * (f y - f x) ^ 2) / a ^ 2 := by
  calc
    _ = ∑ x, ∑ y, μ x * K x y * (if f x * f y ≤ 0 then (1 : ℝ) else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    _ ≤ ∑ x, ∑ y, μ x * K x y *
        ((if |f x| ≤ a then (1 : ℝ) else 0) + (f y - f x) ^ 2 / a ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (sign_failure_pointwise (f x) (f y) a ha)
        (mul_nonneg (hμ x) (hK x y))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc,
        ← Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : |f x| ≤ a
      · simp only [hx, ite_true, mul_one, ← Finset.mul_sum, hrow]
      · simp [hx]

lemma good_mass_complement {μ : ι → ℝ} (hμsum : ∑ x, μ x = 1) (d : ι → ℝ) (c : ℝ) :
    1 - (∑ x, if c < d x then μ x else 0) = ∑ x, if d x ≤ c then μ x else 0 := by
  have h : (∑ x, if c < d x then μ x else 0) +
      (∑ x, if d x ≤ c then μ x else 0) = 1 := by
    rw [← hμsum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : c < d x <;> simp [hx, not_le.mpr, le_of_not_gt]
  linarith

lemma sign_good_mass_bound {μ : ι → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμsum : ∑ x, μ x = 1)
    (flip : Equiv.Perm ι) (hflip : ∀ x, μ (flip x) = μ x)
    {K : Matrix ι ι ℝ} (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1)
    (f : ι → ℝ) (hodd : ∀ x, f (flip x) = -f x) (a : ℝ) (ha : 0 < a) :
    1 - (∑ x, if (1 / 4 : ℝ) < (1 / 2 : ℝ) * ∑ y, |K x y - μ y| then μ x else 0) ≤
      4 * ((∑ x, if |f x| ≤ a then μ x else 0) +
        (∑ x, ∑ y, μ x * K x y * (f y - f x) ^ 2) / a ^ 2) := by
  rw [good_mass_complement hμsum]
  calc
    _ ≤ 4 * ∑ x, μ x * ∑ y, if f x * f y ≤ 0 then K x y else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      have her := sign_row_test (hrow x) hμsum f (f x)
        (odd_halfspace_mass_le hμ hμsum flip hflip f hodd (f x))
      have herr0 : 0 ≤ ∑ y, if f x * f y ≤ 0 then K x y else 0 := by
        apply Finset.sum_nonneg
        intro y _
        split_ifs <;> first | exact hK x y | exact le_rfl
      split_ifs with hd
      · have hlower : (1 / 4 : ℝ) ≤ ∑ y, if f x * f y ≤ 0 then K x y else 0 := by
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hlower (hμ x)]
      · exact mul_nonneg (by norm_num) (mul_nonneg (hμ x) herr0)
    _ ≤ _ := mul_le_mul_of_nonneg_left (sign_failure_average hμ hK hrow f a ha) (by norm_num)

end SignTest

variable {n : ℕ} (W : Disorder n)

theorem continuous_good_mass_bound (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t)
    (a : Fin n → ℝ) (b : ℝ) (hb : 0 < b) :
    1 - continuousGoodMass W t ≤
      4 * ((∑ x, if |linearObservable a x| ≤ b then gibbs W x else 0) +
        (2 * t * ∑ i, a i ^ 2) / b ^ 2) := by
  have htest := sign_good_mass_bound (gibbs_nonneg W) (gibbs_sum W) spinFlipEquiv
    (gibbs_spinFlip W) (continuousKernel_nonneg W hn t ht) (continuousKernel_sum W hn t)
    (linearObservable a) (linearObservable_spinFlip a) b hb
  change 1 - continuousGoodMass W t ≤ _ at htest
  refine le_trans htest ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (sq_nonneg b)
  exact (stationary_increment_continuous W hn t ht (linearObservable a)).trans
    (mul_le_mul_of_nonneg_left (dirichlet_linear_le W a) (by positivity))

theorem discrete_good_mass_bound (hn : 0 < n) (k : ℕ)
    (a : Fin n → ℝ) (b : ℝ) (hb : 0 < b) :
    1 - discreteGoodMass W k ≤
      4 * ((∑ x, if |linearObservable a x| ≤ b then gibbs W x else 0) +
        ((2 * k : ℝ) / n * ∑ i, a i ^ 2) / b ^ 2) := by
  have htest := sign_good_mass_bound (gibbs_nonneg W) (gibbs_sum W) spinFlipEquiv
    (gibbs_spinFlip W) (kernel_pow_nonneg (discreteKernel_nonneg W) k)
    (kernel_pow_sum (discreteKernel_sum W hn) k)
    (linearObservable a) (linearObservable_spinFlip a) b hb
  change 1 - discreteGoodMass W k ≤ _ at htest
  refine le_trans htest ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (sq_nonneg b)
  exact (stationary_increment_discrete W hn k (linearObservable a)).trans
    (mul_le_mul_of_nonneg_left (dirichlet_linear_le W a) (by positivity))

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Cavity
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory

variable {n : ℕ}

lemma flipSite_ne (i : Fin n) (x : Spin n) : flipSite i x ≠ x := by
  intro hh
  have he := congrFun hh i
  simp only [flipSite_apply_self] at he
  cases h : x i <;> simp_all

lemma sameExcept_flipSite (i : Fin n) (x : Spin n) : sameExcept i x (flipSite i x) := by
  intro j hj
  exact flipSite_apply_ne i x hj

lemma sameExcept_two (i : Fin n) (x y : Spin n) :
    sameExcept i x y ↔ y=x ∨ y=flipSite i x := by
  constructor
  · intro h
    by_cases he : y i=x i
    · left
      funext j
      by_cases hj : j=i
      · simpa only [hj] using he
      · exact h j hj
    · right
      funext j
      by_cases hj : j=i
      · subst j
        simp only [flipSite_apply_self]
        cases hx : x i <;> cases hy : y i <;> simp_all
      · rw [flipSite_apply_ne i x hj]
        exact h j hj
  · rintro (h|h)
    · subst y; exact sameExcept_refl i x
    · subst y; exact sameExcept_flipSite i x

lemma sum_sameExcept (i : Fin n) (x : Spin n) (f : Spin n → ℝ) :
    (∑ y : Spin n, if sameExcept i x y then f y else 0) = f x+f (flipSite i x) := by
  classical
  have he (y : Spin n) : (if sameExcept i x y then f y else 0) =
      (if y=x then f x else 0)+(if y=flipSite i x then f (flipSite i x) else 0) := by
    simp only [sameExcept_two]
    have hne := flipSite_ne i x
    split_ifs <;> simp_all
  simp_rw [he]
  simp [Finset.sum_add_distrib]

lemma siteAverage_two (W : Disorder n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    siteAverage W i f x = (gibbs W x*f x+gibbs W (flipSite i x)*f (flipSite i x))/(gibbs W x+gibbs W (flipSite i x)) := by
  rw [siteAverage_eq]
  simp only [siteKernel]
  have he (y : Spin n) : (if sameExcept i x y then gibbs W y/(∑ z, if sameExcept i x z then gibbs W z else 0) else 0)*f y =
      (if sameExcept i x y then gibbs W y*f y else 0)/(∑ z, if sameExcept i x z then gibbs W z else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [← Finset.sum_div,sum_sameExcept,sum_sameExcept]

end

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_CubeRestriction
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set
namespace CriticalSK

lemma integral_dominates_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {E : Set Ω} {f : Ω → ℝ}
    (hi : Integrable f μ) (hf : ∀ x, 0 ≤ f x) (he : ∀ x ∈ E, 1 ≤ f x) :
    μ.real E ≤ ∫ x, f x ∂μ := by
  apply (measureReal_mono (show E ⊆ {x | 1 ≤ f x} from he)).trans
  simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hf) hi 1

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMatrices
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace
open Module
namespace CriticalSK


section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[simp] lemma upperRead_upperWrite (a : UpperEntry ι → ℝ) :
    upperRead (upperWrite a) = a := by
  funext p
  exact dite_eq_left p.2

end Upper

open scoped BigOperators

end

open scoped BigOperators

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

open Set MeasureTheory Filter

lemma third_power_square {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma fifth_third_power {x : ℝ} (hx : 0 < x) : x^(5/3:ℝ) = x*x^(2/3:ℝ) := by
  rw [show (5/3:ℝ) = 1+2/3 by ring,Real.rpow_add hx,Real.rpow_one]

open Set Filter MeasureTheory

lemma rpow_ratio_tendsto_zero {a ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n:ℝ)^(a-ε)/(n:ℝ)^a) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [Function.comp_def]
  rw [← Real.rpow_sub (Nat.cast_pos.mpr hn)]
  congr 1
  ring

lemma ceil_rpow_ratio_tendsto_zero {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (⌈(n:ℝ)^(a-ε)⌉₊:ℝ)/(n:ℝ)^a) atTop (𝓝 0) := by
  have he := (rpow_ratio_tendsto_zero (a := a) hε).add
    (((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop))
  rw [zero_add] at he
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) _ he
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ (n:ℝ)^(a-ε) by positivity)).le
  have hp : 0 < (n:ℝ)^a := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) a
  calc
    _ ≤ ((n:ℝ)^(a-ε)+1)/(n:ℝ)^a := div_le_div_of_nonneg_right hc hp.le
    _ = _ := by simp only [Function.comp_def]; rw [add_div,one_div,Real.rpow_neg (Nat.cast_nonneg n)]

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_TriNoise
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

lemma dyadic_cube_scale (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ∧
    ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ≤ 8 * N := by
  have he : ((2 : ℝ)^Nat.clog 8 N) ^ 3 = (8 : ℝ)^Nat.clog 8 N := by
    rw [← pow_mul, mul_comm (Nat.clog 8 N) 3, pow_mul]
    norm_num
  rw [he]
  constructor
  · exact_mod_cast Nat.le_pow_clog (by decide : 1 < 8) N
  · by_cases hn : N = 1
    · subst N
      norm_num [Nat.clog_one_right]
    · have hn' : 1 < N := by omega
      have hi := Nat.pow_pred_clog_lt_self (by decide : 1 < 8) hn'
      have hj := Nat.clog_pos (by decide : 1 < 8) hn'
      have hid : Nat.clog 8 N = (Nat.clog 8 N).pred + 1 := by
        simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj).symm
      rw [hid, pow_succ]
      have hi' : (8 : ℝ)^(Nat.clog 8 N).pred < N := by exact_mod_cast hi
      linarith

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_DisorderTransfer
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set

namespace CriticalSK

section

lemma symmetric_sum_upper {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i)+2*∑ e : Edge n, f e.val.1 e.val.2 := by
  classical
  have hu : (∑ e : Edge n, f e.val.1 e.val.2) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Fintype.sum_prod_type' (fun i j : Fin n => if i < j then f i j else 0)]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (by intro p; simp) (fun p : Fin n × Fin n => f p.1 p.2)).symm
  rw [hu]
  have hl : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [hf j i]
  have hd : (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by simp
  calc
    _ = (∑ i, ∑ j, if i = j then f i j else 0)+
        (∑ i, ∑ j, if i < j then f i j else 0)+(∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h,ne_of_lt h,not_lt_of_ge h.le]
      · subst j; simp
      · simp [h,ne_of_gt h,not_lt_of_ge h.le]
    _ = _ := by rw [hd,hl]; ring

lemma gibbs_continuous {n : ℕ} (x : Spin n) : Continuous (fun W : Disorder n => gibbs W x) := by
  apply Continuous.div
  · unfold hamiltonian; fun_prop
  · unfold partition hamiltonian; fun_prop
  · exact fun W => (partition_pos W).ne'

open scoped NNReal

end

open Set MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_EdgeAsymptotics
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK


open scoped Topology

lemma edgeLength_pos (n : ℕ) : 0 < edgeLength n := by unfold edgeLength; positivity

lemma edgeLength_cast_pos (n : ℕ) : (0:ℝ) < edgeLength n := by exact_mod_cast edgeLength_pos n

lemma edgeLength_cube (n : ℕ) : (n+1:ℝ) ≤ (edgeLength n:ℝ)^3 ∧
    (edgeLength n:ℝ)^3 ≤ 8*(n+1:ℝ) := by
  simpa only [edgeLength,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
    dyadic_cube_scale (n+1) (Nat.succ_pos n)

open scoped Topology

lemma edgeFixedCost_tendsto (h : ℝ) : Tendsto (edgeFixedCost h) atTop (𝓝 0) := by
  have hA := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/8)).const_mul
    (416*formConstant*(h+1))
  have hB := (tendsto_id.atTop_mul_atTop₀ Real.tendsto_sqrt_atTop).const_div_atTop (16:ℝ)
  have ht : Tendsto (fun L => edgeFixedCost h L) atTop (𝓝 0) := by
    simpa only [edgeFixedCost,neg_div,mul_zero,zero_add,id_eq] using hA.add hB
  exact ht

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_OrientationLimits
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK


lemma cutoff_cubic_identity {x : ℝ} (hx : 0 < x) :
    x*(x^(-(7/24:ℝ)))^3 = x^(1/8:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  conv_lhs => lhs; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  norm_num

lemma rpow_exp_small_tendsto (p : ℝ) :
    Tendsto (fun n : ℕ => (n+1:ℝ)^p*Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hx := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp hn
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (8*p) (1/24) (by norm_num)).comp hx
  apply hh.congr
  intro n
  change ((n+1:ℝ)^(1/8:ℝ))^(8*p)*_ = _
  rw [← Real.rpow_mul (by positivity)]
  congr 2
  ring

lemma edgeLength_sq_le_linear (n : ℕ) : (edgeLength n:ℝ)^2 ≤ 8*(n+1) := by
  have hd : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hcube := (edgeLength_cube n).2
  have hh : (edgeLength n:ℝ)^2 ≤ (edgeLength n:ℝ)^3 := by nlinarith [sq_nonneg ((edgeLength n:ℝ)-1)]
  exact hh.trans hcube

lemma naturalPartitionBase_pos {L : ℝ} (hL : 0 < L) : 0 < naturalPartitionBase L := by
  unfold naturalPartitionBase
  positivity

lemma naturalPartitionConstant_lower (n : ℕ) {L : ℝ} (hL : 0 < L) :
    naturalPartitionBase L/(n+1) ≤ naturalPartitionConstant n L := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hd := edgeLength_cast_pos n
  have hh := div_le_div_of_nonneg_left hL.le (pow_pos hd 2) (edgeLength_sq_le_linear n)
  have ht := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 4))
    (Real.exp_pos (-6*(L*Real.sqrt L))).le
  unfold naturalPartitionBase naturalPartitionConstant naturalEdgeScale
  calc
    _ = L/(8*(n+1))/4*Real.exp (-6*(L*Real.sqrt L)) := by
      field_simp
      ring
    _ ≤ _ := ht

lemma naturalPartitionConstant_pos (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < naturalPartitionConstant n L :=
  (div_pos (naturalPartitionBase_pos hL) (by positivity)).trans_le (naturalPartitionConstant_lower n hL)

lemma naturalOrientationTail_bound (n : ℕ) {L : ℝ} (hL : 0 < L) :
    naturalOrientationTail n L ≤ 2*(26*Real.exp 1/naturalPartitionBase L)^2*(n+1:ℝ)^5*
      Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ)) := by
  have hN : (0:ℝ) < n+1 := by positivity
  have hK := naturalPartitionConstant_pos n hL
  have hB := naturalPartitionBase_pos hL
  have he : -(n+1:ℝ)/24*overlapCentralCutoff (n+1)^3 = -(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ) := by
    have hi := cutoff_cubic_identity hN
    unfold overlapCentralCutoff
    push_cast
    linear_combination -(1/24:ℝ)*hi
  have hratio : 26*Real.exp 1*(n+1)/naturalPartitionConstant n L ≤
      (26*Real.exp 1/naturalPartitionBase L)*(n+1)^2 := by
    apply (div_le_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left (naturalPartitionConstant_lower n hL)
      (show 0 ≤ (26*Real.exp 1/naturalPartitionBase L)*(n+1:ℝ)^2 by positivity)
    apply le_trans _ hh
    apply le_of_eq
    field_simp
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 26*Real.exp 1*(n+1:ℝ)/naturalPartitionConstant n L) hratio 2
  have hfac : (n+2:ℝ) ≤ 2*(n+1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold naturalOrientationTail
  rw [he]
  have hh := mul_le_mul hfac (mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))).le)
    (by positivity) (by positivity : (0:ℝ) ≤ 2*(n+1))
  apply hh.trans_eq
  ring

lemma naturalOrientationTail_scaled_tendsto {L : ℝ} (hL : 0 < L) (p : ℝ) :
    Tendsto (fun n : ℕ => (n+1:ℝ)^p*naturalOrientationTail n L) atTop (𝓝 0) := by
  have ht := (rpow_exp_small_tendsto (p+5)).const_mul (2*(26*Real.exp 1/naturalPartitionBase L)^2)
  have hz : Tendsto (fun n : ℕ => (n+1:ℝ)^p*
      (2*(26*Real.exp 1/naturalPartitionBase L)^2*(n+1:ℝ)^5*Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.congr (fun n => by
      rw [Real.rpow_add (by positivity),show (5:ℝ) = (5:ℕ) by norm_num, Real.rpow_natCast]
      ring)
  apply squeeze_zero (fun n => by unfold naturalOrientationTail; positivity) (fun n =>
    mul_le_mul_of_nonneg_left (naturalOrientationTail_bound n hL) (Real.rpow_nonneg (by positivity) _)) hz

open Set MeasureTheory Filter

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_SmallBall
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK

open Set MeasureTheory Filter

lemma naturalSmallBallConstant_pos {L : ℝ} (hL : 0 < L) : 0 < naturalSmallBallConstant L := by
  unfold naturalSmallBallConstant
  positivity

lemma exists_spectral_failure_parameter {α : ℝ} (hα : 0 < α) :
    ∃ h : ℝ, 0 ≤ h ∧ 32*Real.exp (-h^2) < α := by
  have hh : Tendsto (fun h : ℝ => -h^2) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have ht : Tendsto (fun h : ℝ => 32*Real.exp (-h^2)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hh).const_mul 32
  exact ((eventually_ge_atTop 0).and (ht.eventually (gt_mem_nhds hα))).exists

lemma natural_smallBall_tight {δ α : ℝ} (hδ : 0 < δ) (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      (smallBallObstruction (n+4) (b*(n+4:ℝ)^(1/3:ℝ)) δ) < α := by
  obtain ⟨h,hh,hfail⟩ := exists_spectral_failure_parameter (show 0 < α/4 by positivity)
  obtain ⟨L,hL,hcost⟩ := ((eventually_ge_atTop (262144:ℝ)).and
    ((edgeFixedCost_tendsto h).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)))).exists
  have hLp : 0 < L := by linarith
  let C := naturalSmallBallConstant L
  have hC : 0 < C := naturalSmallBallConstant_pos hLp
  let b := α*δ/(16*C)
  let ε := α*δ/32
  have hb : 0 < b := by dsimp [b]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨b,hb,?_⟩
  have ht : Tendsto (fun n : ℕ => naturalOrientationTail (n+3) L) atTop (𝓝 0) := by
    have hs := (naturalOrientationTail_scaled_tendsto hLp 0).comp (tendsto_add_atTop_nat 3)
    simpa only [Function.comp_def,Real.rpow_zero,one_mul] using hs
  filter_upwards [natural_smallBallObstruction_probability_s2 hh hL hcost hε hb.le hδ,
    ht.eventually (gt_mem_nhds hε)] with n hn htail
  apply lt_of_le_of_lt hn
  have hbc : 2*C*b = α*δ/8 := by dsimp only [b]; field_simp; ring
  change 32*Real.exp (-h^2)+(2*C*b+4*(ε+naturalOrientationTail (n+3) L))/δ < α
  rw [hbc]
  have hfrac : (α*δ/8+4*(ε+naturalOrientationTail (n+3) L))/δ < 3*α/4 := by
    apply (div_lt_iff₀ hδ).mpr
    dsimp only [ε] at htail ⊢
    nlinarith
  linarith

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Equilibrium
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

open Set MeasureTheory Filter

lemma continuousGoodMass_le_one {n : ℕ} (W : Disorder n) (t : ℝ) : continuousGoodMass W t ≤ 1 := by
  rw [← gibbs_sum W]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact gibbs_nonneg W x

lemma discreteGoodMass_le_one {n : ℕ} (W : Disorder n) (k : ℕ) : discreteGoodMass W k ≤ 1 := by
  rw [← gibbs_sum W]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact gibbs_nonneg W x

lemma continuous_bad_subset {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t)
    {a δ : ℝ} (ha : 0 < a) (_hδ : 0 < δ) (hinc : 2*t/a^2 < δ/8) :
    {W : Disorder n | δ ≤ |continuousGoodMass W t-1|} ⊆ smallBallObstruction n a (δ/8) := by
  intro W hW u hu
  have hb := continuous_good_mass_bound W hn t ht u a ha
  change 1-continuousGoodMass W t ≤ 4*(linearSmallBall W u a+(2*t*∑ i, (u i)^2)/a^2) at hb
  rw [← EuclideanSpace.real_norm_sq_eq,hu,one_pow,mul_one] at hb
  have he : |continuousGoodMass W t-1| = 1-continuousGoodMass W t := by
    rw [abs_of_nonpos (sub_nonpos.mpr (continuousGoodMass_le_one W t))]
    ring
  simp only [Set.mem_ofPred_eq,he] at hW
  linarith

lemma discrete_bad_subset {n : ℕ} (hn : 0 < n) (k : ℕ)
    {a δ : ℝ} (ha : 0 < a) (_hδ : 0 < δ) (hinc : ((2*k:ℝ)/n)/a^2 < δ/8) :
    {W : Disorder n | δ ≤ |discreteGoodMass W k-1|} ⊆ smallBallObstruction n a (δ/8) := by
  intro W hW u hu
  have hb := discrete_good_mass_bound W hn k u a ha
  change 1-discreteGoodMass W k ≤ 4*(linearSmallBall W u a+((2*k:ℝ)/n*∑ i, (u i)^2)/a^2) at hb
  rw [← EuclideanSpace.real_norm_sq_eq,hu,one_pow,mul_one] at hb
  have he : |discreteGoodMass W k-1| = 1-discreteGoodMass W k := by
    rw [abs_of_nonpos (sub_nonpos.mpr (discreteGoodMass_le_one W k))]
    ring
  simp only [Set.mem_ofPred_eq,he] at hW
  linarith

lemma realized_continuous_initial_states (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hscale : Tendsto (fun n => t n/(n:ℝ)^(2/3:ℝ)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real {W | δ ≤ |continuousGoodMass W (t n)-1|}) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha measureReal_nonneg)
  · intro α hα
    obtain ⟨b,hb,hprob⟩ := natural_smallBall_tight (show 0 < δ/8 by positivity) hα
    have hinc : Tendsto (fun n : ℕ => 2*t (n+4)/(b*(n+4:ℝ)^(1/3:ℝ))^2) atTop (𝓝 0) := by
      have hh := (hscale.comp (tendsto_add_atTop_nat 4)).const_mul (2/b^2)
      convert hh using 1
      · ext n
        simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,mul_pow,third_power_square (by positivity : (0:ℝ) ≤ n+4)]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      · ring_nf
    filter_upwards [hprob,hinc.eventually (gt_mem_nhds (show 0 < δ/8 by positivity))] with n hn hi
    exact lt_of_le_of_lt (measureReal_mono (continuous_bad_subset (by omega : 0 < n+4)
      (t (n+4)) (ht _) (by positivity) hδ hi)) hn

lemma realized_discrete_initial_states (k : ℕ → ℕ)
    (hscale : Tendsto (fun n => (k n:ℝ)/(n:ℝ)^(5/3:ℝ)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real {W | δ ≤ |discreteGoodMass W (k n)-1|}) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha measureReal_nonneg)
  · intro α hα
    obtain ⟨b,hb,hprob⟩ := natural_smallBall_tight (show 0 < δ/8 by positivity) hα
    have hinc : Tendsto (fun n : ℕ => ((2*k (n+4):ℝ)/(n+4:ℝ))/(b*(n+4:ℝ)^(1/3:ℝ))^2) atTop (𝓝 0) := by
      have hh := (hscale.comp (tendsto_add_atTop_nat 4)).const_mul (2/b^2)
      convert hh using 1
      · ext n
        simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,mul_pow,
          third_power_square (by positivity : (0:ℝ) ≤ n+4), fifth_third_power (by positivity : (0:ℝ) < n+4)]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      · ring_nf
    filter_upwards [hprob,hinc.eventually (gt_mem_nhds (show 0 < δ/8 by positivity))] with n hn hi
    exact lt_of_le_of_lt (measureReal_mono (discrete_bad_subset (by omega : 0 < n+4)
      (k (n+4)) (by positivity) hδ (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hi))) hn

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GapMixing
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators Topology

open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators Topology
namespace CriticalSK


section

open Set Filter MeasureTheory

variable {n : ℕ} (W V : Disorder n)

lemma mean_square_center_identity (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => (f x-c)^2) = variance W f+(mean W f-c)^2 := by
  have hs : mean W (fun x => (f x-c)^2) = mean W (fun x => f x^2)-2*c*mean W f+c^2 := by
    have he : (fun x => (f x-c)^2) = (fun x => f x^2-(2*c)*f x+c^2) := by funext x; ring
    rw [he,mean_add,mean_sub,mean_const_mul,mean_const]
  have hv : variance W f = mean W (fun x => f x^2)-(mean W f)^2 := by
    unfold variance
    have he : (fun x => (f x-mean W f)^2) = (fun x => f x^2-(2*mean W f)*f x+(mean W f)^2) := by funext x; ring
    rw [he,mean_add,mean_sub,mean_const_mul,mean_const]
    ring
  rw [hs,hv]
  ring

lemma mean_least_squares (f : Spin n → ℝ) (c : ℝ) :
    variance W f ≤ mean W (fun x => (f x-c)^2) := by
  rw [mean_square_center_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma mean_density_upper {M : ℝ} (hM : ∀ x, gibbs W x ≤ M*gibbs V x)
    (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x) : mean W f ≤ M*mean V f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  nlinarith [mul_le_mul_of_nonneg_right (hM x) (hf x)]

lemma variance_density_upper {M : ℝ} (hM : ∀ x, gibbs W x ≤ M*gibbs V x)
    (f : Spin n → ℝ) : variance W f ≤ M*variance V f :=
  (mean_least_squares W f (mean V f)).trans (mean_density_upper W V hM _ (fun _ => sq_nonneg _))

lemma dirichlet_density_lower {m : ℝ} (hm : 0 ≤ m) (hden : ∀ x, m*gibbs V x ≤ gibbs W x)
    (f : Spin n → ℝ) : m*dirichlet V f ≤ dirichlet W f := by
  unfold dirichlet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change m*mean V (fun x => (f x-siteAverage V i f x)^2) ≤ mean W (fun x => (f x-siteAverage W i f x)^2)
  have hh := siteAverage_least_squares V i f (siteAverage W i f) (fun x y h => (siteAverage_fiber_constant W i f h).symm)
  refine (mul_le_mul_of_nonneg_left hh hm).trans ?_
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  nlinarith [mul_le_mul_of_nonneg_right (hden x) (sq_nonneg (f x-siteAverage W i f x))]

lemma poincare_density_comparison {m M C : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hlower : ∀ x, m*gibbs V x ≤ gibbs W x) (hupper : ∀ x, gibbs W x ≤ M*gibbs V x)
    (hgap : ∀ f : Spin n → ℝ, variance V f ≤ C*dirichlet V f) (f : Spin n → ℝ) :
    variance W f ≤ (M/m*C)*dirichlet W f := by
  have hu := (variance_density_upper W V hupper f).trans (mul_le_mul_of_nonneg_left (hgap f) hM)
  have hl := dirichlet_density_lower W V hm.le hlower f
  have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hM hC)
  have he : (M/m*C)*dirichlet W f = (M*C*dirichlet W f)/m := by ring
  rw [he]
  apply (le_div_iff₀ hm).mpr
  have ht := mul_le_mul_of_nonneg_right hu hm.le
  nlinarith only [hh,ht]

lemma hamiltonian_scale (β : ℝ) (x : Spin n) : hamiltonian (β • W) x = β*hamiltonian W x := by
  simp only [hamiltonian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma gibbs_scale_ratio (β : ℝ) (x : Spin n) : gibbs W x =
    (partition (β • W)/partition W)*Real.exp ((1-β)*hamiltonian W x)*gibbs (β • W) x := by
  rw [gibbs,gibbs,hamiltonian_scale]
  have he : Real.exp ((1-β)*hamiltonian W x)*Real.exp (β*hamiltonian W x) = Real.exp (hamiltonian W x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp [ne_of_gt (partition_pos W),ne_of_gt (partition_pos (β • W))]
  nlinarith only [he]

lemma poincare_temperature_comparison {β R C : ℝ} (hβ : β ≤ 1) (hC : 0 ≤ C)
    (hH : ∀ x, |hamiltonian W x| ≤ R)
    (hgap : ∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f) (f : Spin n → ℝ) :
    variance W f ≤ (C*Real.exp (2*(1-β)*R))*dirichlet W f := by
  let z := partition (β • W)/partition W
  have hz : 0 < z := div_pos (partition_pos _) (partition_pos _)
  let m := z*Real.exp (-(1-β)*R)
  let M := z*Real.exp ((1-β)*R)
  have hm : 0 < m := mul_pos hz (Real.exp_pos _)
  have hM : 0 ≤ M := (mul_pos hz (Real.exp_pos _)).le
  have hl (x : Spin n) : m*gibbs (β • W) x ≤ gibbs W x := by
    rw [gibbs_scale_ratio W β x]
    apply mul_le_mul_of_nonneg_right _ (gibbs_nonneg _ _)
    apply mul_le_mul_of_nonneg_left _ hz.le
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (abs_le.mp (hH x)).1 (sub_nonneg.mpr hβ)
    nlinarith only [ht]
  have hu (x : Spin n) : gibbs W x ≤ M*gibbs (β • W) x := by
    rw [gibbs_scale_ratio W β x]
    apply mul_le_mul_of_nonneg_right _ (gibbs_nonneg _ _)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hH x)).2 (sub_nonneg.mpr hβ))) hz.le
  have hh := poincare_density_comparison W (β • W) hm hM hC hl hu hgap f
  have he : M/m*C = C*Real.exp (2*(1-β)*R) := by
    dsimp [M,m]
    rw [mul_div_mul_left _ _ hz.ne',← Real.exp_sub]
    rw [mul_comm]
    congr 2
    ring
  rwa [he] at hh

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma mean_kernel (K : Matrix (Spin n) (Spin n) ℝ)
    (hstat : ∀ y, ∑ x, gibbs W x*K x y = gibbs W y) (f : Spin n → ℝ) : mean W (K.mulVec f) = mean W f := by
  unfold mean Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← mul_assoc,← Finset.sum_mul,hstat]

lemma discreteKernel_quadratic_eq (f : Spin n → ℝ) :
    mean W (fun x => f x*(discreteKernel W).mulVec f x) =
      (n:ℝ)⁻¹*∑ i : Fin n, mean W (fun x => (siteAverage W i f x)^2) := by
  simp_rw [discreteKernel_average,mul_left_comm (f _),Finset.mul_sum,mean_sum,mean_const_mul,siteAverage_self_square]

lemma discreteKernel_square_le (hn : 0<n) (f : Spin n → ℝ) :
    mean W (fun x => ((discreteKernel W).mulVec f x)^2) ≤
      mean W (fun x => f x^2)-dirichlet W f/n := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hp (x : Spin n) : ((discreteKernel W).mulVec f x)^2 ≤ (n:ℝ)⁻¹*∑ i : Fin n, (siteAverage W i f x)^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _i : Fin n => (1:ℝ)) (fun i => siteAverage W i f x)
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    rw [discreteKernel_average,← div_eq_inv_mul,div_pow,← div_eq_inv_mul]
    apply (div_le_div_iff₀ (sq_pos_of_pos hnpos) hnpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hh hnpos.le]
  have hm := mean_mono W hp
  rw [mean_const_mul,mean_sum,← discreteKernel_quadratic_eq] at hm
  have hd := dirichlet_discrete W hn f
  have he : mean W (fun x => f x*(f x-(discreteKernel W).mulVec f x)) =
      mean W (fun x => f x^2)-mean W (fun x => f x*(discreteKernel W).mulVec f x) := by
    rw [← mean_sub]
    congr 1
    funext x
    ring
  rw [he] at hd
  linarith

lemma gap_factor_nonneg (hn : 0<n) {C : ℝ} (hC : 1≤C) : 0 ≤ 1-1/((n:ℝ)*C) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hnc : 1≤(n:ℝ)*C := le_trans hC (le_mul_of_one_le_left (le_trans zero_le_one hC) hn1)
  have hpos : 0<(n:ℝ)*C := lt_of_lt_of_le zero_lt_one hnc
  exact sub_nonneg.mpr ((div_le_one hpos).mpr hnc)

lemma gap_square_step (hn : 0<n) {C : ℝ} (hC : 0<C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (f : Spin n → ℝ) (hf : mean W f=0) :
    mean W (fun x => ((discreteKernel W).mulVec f x)^2) ≤
      (1-1/((n:ℝ)*C))*mean W (fun x => f x^2) := by
  have hg := hgap f
  simp only [variance,hf,sub_zero] at hg
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hd : mean W (fun x => f x^2)/((n:ℝ)*C) ≤ dirichlet W f/n := by
    apply (div_le_div_iff₀ (mul_pos hnpos hC) hnpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hg hnpos.le]
  have hs := discreteKernel_square_le W hn f
  have he : (1-1/((n:ℝ)*C))*mean W (fun x => f x^2) = mean W (fun x => f x^2)-mean W (fun x => f x^2)/((n:ℝ)*C) := by ring
  rw [he]
  linarith

lemma gap_square_pow (hn : 0<n) {C : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (f : Spin n → ℝ) (hf : mean W f=0) (k : ℕ) :
    mean W (fun x => ((discreteKernel W^k).mulVec f x)^2) ≤
      (1-1/((n:ℝ)*C))^k*mean W (fun x => f x^2) := by
  induction k with
  | zero => simp only [pow_zero,Matrix.one_mulVec,one_mul,le_refl]
  | succ k ih =>
    have hzero : mean W ((discreteKernel W^k).mulVec f)=0 := by rw [mean_kernel W _ (kernel_pow_stationary (discreteKernel_stationary W hn) k),hf]
    have hs := gap_square_step W hn (lt_of_lt_of_le zero_lt_one hC) hgap _ hzero
    rw [pow_succ',← Matrix.mulVec_mulVec]
    refine hs.trans ?_
    rw [pow_succ']
    exact (mul_le_mul_of_nonneg_left ih (gap_factor_nonneg hn hC)).trans_eq (mul_assoc _ _ _).symm

lemma gap_square_exponential (hn : 0<n) {C : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (f : Spin n → ℝ) (hf : mean W f=0) (k : ℕ) :
    mean W (fun x => ((discreteKernel W^k).mulVec f x)^2) ≤
      Real.exp (-(k:ℝ)/((n:ℝ)*C))*mean W (fun x => f x^2) := by
  refine (gap_square_pow W hn hC hgap f hf k).trans ?_
  apply mul_le_mul_of_nonneg_right _ (mean_nonneg W (fun _ => sq_nonneg _))
  have he : 1-1/((n:ℝ)*C) ≤ Real.exp (-1/((n:ℝ)*C)) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-1/((n:ℝ)*C))
  have hh := pow_le_pow_left₀ (gap_factor_nonneg hn hC) he k
  rw [← Real.exp_nat_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end


section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma kernel_pow_reversible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℝ} {μ : ι → ℝ} (h : ∀ x y, μ x*K x y=μ y*K y x)
    (k : ℕ) (x y : ι) : μ x*(K^k) x y=μ y*(K^k) y x := by
  induction k generalizing x y with
  | zero => simp only [pow_zero,Matrix.one_apply]; split_ifs with he <;> simp_all
  | succ k ih =>
    rw [pow_succ,Matrix.mul_apply,Finset.mul_sum]
    calc
      _ = ∑ z, μ y*K y z*(K^k) z x := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← mul_assoc,ih,mul_assoc,mul_left_comm, h z y]
        ring
      _ = μ y*(K^(k+1)) y x := by rw [pow_succ',Matrix.mul_apply,Finset.mul_sum]; ring_nf

lemma mean_abs_square_le (f : Spin n → ℝ) : (mean W (fun x => |f x|))^2 ≤ mean W (fun x => f x^2) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => Real.sqrt (gibbs W x)) (fun x => Real.sqrt (gibbs W x)*|f x|)
  simp only [mul_pow,Real.sq_sqrt (gibbs_nonneg W _),sq_abs,gibbs_sum,one_mul] at hh
  have he : (∑ x : Spin n, Real.sqrt (gibbs W x)*(Real.sqrt (gibbs W x)*|f x|)) = mean W (fun x => |f x|) := by
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc,Real.mul_self_sqrt (gibbs_nonneg W _)]
  rw [he] at hh
  exact hh

lemma centeredPointDensity_mean (x : Spin n) : mean W (centeredPointDensity W x)=0 := by
  change mean W (fun y => (if y=x then (gibbs W x)⁻¹ else 0)-1)=0
  rw [mean_sub,mean_const]
  unfold mean
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [mul_inv_cancel₀ (gibbs_pos W x).ne',sub_self]

lemma centeredPointDensity_square (x : Spin n) : mean W (fun y => centeredPointDensity W x y ^ 2) = (gibbs W x)⁻¹-1 := by
  have hid (y : Spin n) : centeredPointDensity W x y ^2 = (if y=x then (gibbs W x)⁻¹^2-2*(gibbs W x)⁻¹ else 0)+1 := by
    unfold centeredPointDensity
    split_ifs <;> ring
  simp_rw [hid]
  rw [mean_add,mean_const]
  unfold mean
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp [(gibbs_pos W x).ne']
  ring

lemma centeredPointDensity_kernel (hn : 0<n) (x y : Spin n) (k : ℕ) :
    (discreteKernel W^k).mulVec (centeredPointDensity W x) y =
      (discreteKernel W^k) x y/gibbs W y-1 := by
  have hrev := kernel_pow_reversible (discreteKernel_reversible W) k y x
  unfold Matrix.mulVec dotProduct centeredPointDensity
  simp only [mul_sub,Finset.sum_sub_distrib,mul_one,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [kernel_pow_sum (discreteKernel_sum W hn)]
  have hx := (gibbs_pos W x).ne'
  have hy := (gibbs_pos W y).ne'
  field_simp
  nlinarith only [hrev]

lemma discreteDistance_mean_density (hn : 0<n) (x : Spin n) (k : ℕ) :
    discreteDistance W k x = (1/2:ℝ)*mean W (fun y => |(discreteKernel W^k).mulVec (centeredPointDensity W x) y|) := by
  unfold discreteDistance totalVariation mean
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  change |(discreteKernel W^k) x y-gibbs W y|=gibbs W y*|(discreteKernel W^k).mulVec (centeredPointDensity W x) y|
  rw [centeredPointDensity_kernel W hn]
  symm
  calc
    _ = |gibbs W y| *|(discreteKernel W^k) x y/gibbs W y-1| := by rw [abs_of_nonneg (gibbs_nonneg W y)]
    _ = _ := by
      rw [← abs_mul]
      congr 1
      field_simp [(gibbs_pos W y).ne']

lemma discreteDistance_square_gap (hn : 0<n) {C : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f) (x : Spin n) (k : ℕ) :
    (discreteDistance W k x)^2 ≤ Real.exp (-(k:ℝ)/((n:ℝ)*C))/(4*gibbs W x) := by
  rw [discreteDistance_mean_density W hn,mul_pow]
  have hh := (mean_abs_square_le W ((discreteKernel W^k).mulVec (centeredPointDensity W x))).trans
    (gap_square_exponential W hn hC hgap _ (centeredPointDensity_mean W x) k)
  rw [centeredPointDensity_square] at hh
  have ht := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ (1/2)^2)
  have he := Real.exp_nonneg (-(k:ℝ)/((n:ℝ)*C))
  have hid : Real.exp (-(k:ℝ)/((n:ℝ)*C))/(4*gibbs W x) = (1/2:ℝ)^2*(Real.exp (-(k:ℝ)/((n:ℝ)*C))*(gibbs W x)⁻¹) := by ring
  rw [hid]
  nlinarith only [ht,he]

lemma discreteDistance_gap_bound (hn : 0<n) {C A : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A) ≤ gibbs W x) (x : Spin n) (k : ℕ) :
    discreteDistance W k x ≤ Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2 := by
  have hs := discreteDistance_square_gap W hn hC hgap x k
  have he : Real.exp (-(k:ℝ)/((n:ℝ)*C))/(4*gibbs W x) ≤
      (Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2)^2 := by
    have hμ : 0<gibbs W x := gibbs_pos W x
    have hh := div_le_div_of_nonneg_left (Real.exp_nonneg (-(k:ℝ)/((n:ℝ)*C))) (by positivity : 0<4*Real.exp (-A)) (mul_le_mul_of_nonneg_left (hmin x) (by norm_num : (0:ℝ)≤4))
    refine hh.trans_eq ?_
    rw [div_pow,← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num]
    rw [show (2:ℝ)*((A-(k:ℝ)/((n:ℝ)*C))/2)=A-(k:ℝ)/((n:ℝ)*C) by ring]
    rw [show 4*Real.exp (-A)=Real.exp (-A)*4 by ring,div_mul_eq_div_div,← Real.exp_sub]
    congr 1
    congr 1
    ring
  have hnonneg : 0≤Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2 := by positivity
  nlinarith [hs.trans he,sq_nonneg (discreteDistance W k x+Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2)]

end

section

open Set Filter MeasureTheory

lemma poisson_generating_hasSum (a r : ℝ) :
    HasSum (fun k : ℕ => (Real.exp (-a)*a^k/k.factorial)*r^k) (Real.exp (a*(r-1))) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a*r)).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ,← Real.exp_add,show -a+a*r=a*(r-1) by ring] at h
  apply h.congr_fun
  intro k
  simp only [smul_eq_mul,mul_pow]
  ring

lemma finite_l1_series_bound {ι : Type*} [Fintype ι]
    (F : ℕ → ι → ℝ) (z : ι → ℝ) (g : ℕ → ℝ) (B : ℝ)
    (hf : ∀ y, HasSum (fun k => F k y) (z y)) (hg : HasSum g B)
    (hb : ∀ k, (∑ y, |F k y|) ≤ g k) : (∑ y, |z y|) ≤ B := by
  classical
  have ht : Summable (fun k => ∑ y, |F k y|) :=
    Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hb hg.summable
  have hs (y : ι) : Summable (fun k => |F k y|) := by
    have hc (k : ℕ) : |F k y| ≤ ∑ i : ι, |F k i| :=
      Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => abs_nonneg (F k i)) (Finset.mem_univ y)
    exact Summable.of_nonneg_of_le (fun k => abs_nonneg (F k y)) hc ht
  have he (y : ι) : |z y| ≤ ∑' k, |F k y| :=
    (hf y).norm_le_of_bounded (hs y).hasSum (fun _ => le_rfl)
  calc
    _ ≤ ∑ y, ∑' k, |F k y| := Finset.sum_le_sum (fun y _ => he y)
    _ = ∑' k, ∑ y, |F k y| := (Summable.tsum_finsetSum (fun y _ => hs y)).symm
    _ ≤ B := hasSum_le hb ht.hasSum hg

lemma poisson_l1_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (μ : ι → ℝ) (a : ℝ) (ha : 0≤a) (B r : ℝ) (x : ι)
    (hbound : ∀ k : ℕ, (∑ y, |(K^k) x y-μ y|) ≤ B*r^k) :
    (∑ y, |NormedSpace.exp (a • (K-1)) x y-μ y|) ≤ B*Real.exp (a*(r-1)) := by
  let c : ℕ → ℝ := fun k => Real.exp (-a)*a^k/k.factorial
  have hc (k : ℕ) : 0 ≤ c k := poisson_coeff_nonneg a ha k
  have hgen : HasSum (fun k : ℕ => c k*(B*r^k)) (B*Real.exp (a*(r-1))) := by
    apply ((poisson_generating_hasSum a r).mul_left B).congr_fun
    intro k
    dsimp [c]
    ring
  have hf (y : ι) : HasSum (fun k => c k*((K^k) x y-μ y)) (NormedSpace.exp (a • (K-1)) x y-μ y) := by
    have hh := (matrix_poisson_hasSum K a x y).sub ((poisson_coeff_hasSum a).mul_right (μ y))
    rw [one_mul] at hh
    apply hh.congr_fun
    intro k
    dsimp [c]
    ring
  apply finite_l1_series_bound _ _ _ _ hf hgen
  intro k
  simp only [abs_mul,abs_of_nonneg (hc k),← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hbound k) (hc k)

lemma exp_neg_linear_bound {u : ℝ} (hu : 0≤u) (hu1 : u≤1) : Real.exp (-u) ≤ 1-u/2 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (Real.exp_nonneg (-u))
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  have hp : 0<1+u := by linarith
  have ht : 1≤(1-u/2)*(1+u) := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  apply (mul_le_mul_iff_of_pos_right hp).mp
  nlinarith only [hh,ht]

variable {n : ℕ} (W : Disorder n)

lemma continuousDistance_gap_bound (hn : 0<n) {C A : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A) ≤ gibbs W x) {t : ℝ} (ht : 0≤t) (x : Spin n) :
    continuousDistance W t x ≤ Real.exp (A/2-t/(4*C))/2 := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hCpos : 0<C := lt_of_lt_of_le zero_lt_one hC
  let r := Real.exp (-1/(2*(n:ℝ)*C))
  have hdis (k : ℕ) : (∑ y, |(discreteKernel W^k) x y-gibbs W y|) ≤ Real.exp (A/2)*r^k := by
    have hh := discreteDistance_gap_bound W hn hC hgap hmin x k
    have he : Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2) = Real.exp (A/2)*r^k := by
      dsimp [r]
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    unfold discreteDistance totalVariation at hh
    linarith only [hh]
  have hh := poisson_l1_bound (discreteKernel W) (gibbs W) ((n:ℝ)*t) (mul_nonneg hnpos.le ht) (Real.exp (A/2)) r x hdis
  rw [← continuousKernel_poisson W hn t] at hh
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hnc : 1≤(n:ℝ)*C := le_trans hC (le_mul_of_one_le_left hCpos.le hn1)
  have hu : 0≤1/(2*(n:ℝ)*C) := by positivity
  have hu1 : 1/(2*(n:ℝ)*C)≤1 := by
    apply (div_le_one (by positivity : 0<2*(n:ℝ)*C)).mpr
    nlinarith only [hnc]
  have hr : r≤1-1/(2*(n:ℝ)*C)/2 := by simpa only [r,neg_div] using exp_neg_linear_bound hu hu1
  have hrate : (n:ℝ)*t*(r-1) ≤ -t/(4*C) := by
    have hs := mul_le_mul_of_nonneg_left (sub_le_sub_right hr 1) (mul_nonneg hnpos.le ht)
    have he : (n:ℝ)*t*((1-1/(2*(n:ℝ)*C)/2)-1) = -t/(4*C) := by field_simp; ring
    rwa [he] at hs
  have hex := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (Real.exp_nonneg (A/2))
  have hfinal : Real.exp (A/2)*Real.exp (-t/(4*C)) = Real.exp (A/2-t/(4*C)) := by rw [← Real.exp_add]; congr 1; ring
  rw [hfinal] at hex
  unfold continuousDistance totalVariation
  linarith only [hh,hex]

end

open Set Filter MeasureTheory

lemma exp_neg_two_le_half : Real.exp (-2) ≤ (1/2:ℝ) := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp 2) (Real.exp_nonneg (-2))
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  linarith [Real.exp_nonneg (-2)]

variable {n : ℕ} (W : Disorder n)

lemma gibbs_lower_of_energy_bound {R : ℝ} (hH : ∀ x, |hamiltonian W x|≤R) (x : Spin n) :
    Real.exp (-(2*R+(n:ℝ))) ≤ gibbs W x := by
  have hcard : (Fintype.card (Spin n):ℝ) ≤ Real.exp (n:ℝ) := by
    have he : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) he n
    rw [← Real.exp_nat_mul,mul_one] at hh
    simpa only [Spin,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hz : partition W ≤ Real.exp (R+(n:ℝ)) := by
    calc
      _ ≤ ∑ _x : Spin n, Real.exp R := Finset.sum_le_sum (fun x _ => Real.exp_le_exp.mpr (abs_le.mp (hH x)).2)
      _ = (Fintype.card (Spin n):ℝ)*Real.exp R := by simp
      _ ≤ Real.exp (n:ℝ)*Real.exp R := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (R+(n:ℝ)) := by rw [← Real.exp_add,add_comm]
  unfold gibbs
  apply (le_div_iff₀ (partition_pos W)).mpr
  calc
    _ ≤ Real.exp (-(2*R+(n:ℝ)))*Real.exp (R+(n:ℝ)) := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (hamiltonian W x) := Real.exp_le_exp.mpr (abs_le.mp (hH x)).1

lemma continuousMixingTime_le_of_distance {t : ℝ} (ht : 0≤t)
    (hd : ∀ x, continuousDistance W t x ≤ 1/4) : continuousMixingTime W ≤ t := by
  apply csInf_le (show BddBelow {s : ℝ | 0 ≤ s ∧ ∀ x, continuousDistance W s x≤1/4} from ⟨0,fun _ hs => hs.1⟩)
  exact ⟨ht,hd⟩

lemma discreteMixingTime_le_of_distance {k : ℕ}
    (hd : ∀ x, discreteDistance W k x ≤ 1/4) : discreteMixingTime W ≤ k := Nat.sInf_le hd

lemma finite_continuous_gap_mixing (hn : 0<n) {C A : ℝ} (hC : 1≤C) (hA : 0≤A)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A)≤gibbs W x) :
    continuousMixingTime W ≤ 4*C*(A+4) := by
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  have ht : 0≤4*C*(A+4) := by positivity
  apply continuousMixingTime_le_of_distance W ht
  intro x
  have hh := continuousDistance_gap_bound W hn hC hgap hmin ht x
  have he : A/2-(4*C*(A+4))/(4*C) ≤ -2 := by
    field_simp
    nlinarith
  have hb := Real.exp_le_exp.mpr he
  have hexp := exp_neg_two_le_half
  linarith

lemma finite_discrete_gap_mixing (hn : 0<n) {C A : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A)≤gibbs W x) {k : ℕ} (hk : (n:ℝ)*C*(A+4)≤k) :
    discreteMixingTime W ≤ k := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  apply discreteMixingTime_le_of_distance W
  intro x
  have hh := discreteDistance_gap_bound W hn hC hgap hmin x k
  have he : (A-(k:ℝ)/((n:ℝ)*C))/2 ≤ -2 := by
    have hq : A+4 ≤ (k:ℝ)/((n:ℝ)*C) := (le_div_iff₀ (mul_pos hnpos hCp)).mpr (by nlinarith only [hk])
    linarith
  have hb := Real.exp_le_exp.mpr he
  linarith [exp_neg_two_le_half]

lemma finite_gap_mixing_bounds (hn : 0<n) {C R : ℝ} (hC : 1≤C) (hR : 0≤R)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hH : ∀ x, |hamiltonian W x|≤R) :
    continuousMixingTime W ≤ 4*C*(2*R+n+4) ∧
    (discreteMixingTime W:ℝ) ≤ (n:ℝ)*C*(2*R+n+4)+1 := by
  constructor
  · exact finite_continuous_gap_mixing W hn hC (by positivity) hgap (gibbs_lower_of_energy_bound W hH)
  · let a := (n:ℝ)*C*(2*R+n+4)
    have ha : 0≤a := by dsimp [a]; positivity
    have hk : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
    have hm := finite_discrete_gap_mixing W hn hC hgap (gibbs_lower_of_energy_bound W hH) hk
    exact (Nat.cast_le.mpr hm).trans (Nat.ceil_lt_add_one ha).le

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Mixing
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter

section KernelContraction

variable {ι : Type*} [Fintype ι]

lemma kernel_l1_contraction {K : Matrix ι ι ℝ} {μ p : ι → ℝ} {c : ℝ}
    (hmass : ∑ x, p x = ∑ x, μ x)
    (hminor : ∀ x y, c ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, ∑ x, μ x*K x y = μ y) :
    (∑ y, |(∑ x, p x*K x y)-μ y|) ≤
      (1-Fintype.card ι*c)*(∑ x, |p x-μ x|) := by
  have hid (y : ι) : (∑ x, p x*K x y)-μ y = ∑ x, (p x-μ x)*(K x y-c) := by
    simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hstat,hmass]
    ring
  simp_rw [hid]
  calc
    _ ≤ ∑ y, ∑ x, |(p x-μ x)*(K x y-c)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ x, |p x-μ x| *(1-Fintype.card ι*c) := by
      simp_rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hminor _ _))]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum,Finset.sum_sub_distrib,hrow]
      simp
    _ = _ := by rw [← Finset.sum_mul,mul_comm]

lemma kernel_row_l1_le_two {K : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hμ : ∀ y, 0 ≤ μ y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hmass : ∑ y, μ y = 1) (x : ι) :
    ∑ y, |K x y-μ y| ≤ 2 := by
  calc
    _ ≤ ∑ y, (K x y+μ y) := Finset.sum_le_sum (fun y _ => by
      simpa only [abs_of_nonneg (hK x y),abs_of_nonneg (hμ y)] using abs_sub (K x y) (μ y))
    _ = 2 := by rw [Finset.sum_add_distrib,hrow,hmass]; norm_num

variable [DecidableEq ι]

lemma strictly_positive_kernel_mixes [Nonempty ι] {K : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hK : ∀ x y, 0 < K x y) (hμ : ∀ y, 0 ≤ μ y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hmass : ∑ y, μ y = 1)
    (hstat : ∀ y, ∑ x, μ x*K x y = μ y) :
    ∃ k : ℕ, ∀ x, (1/2:ℝ)*(∑ y, |(K^k) x y-μ y|) ≤ 1/4 := by
  classical
  let T : Finset ℝ := Finset.univ.image (fun p : ι×ι => K p.1 p.2)
  have hT : T.Nonempty := Finset.Nonempty.image Finset.univ_nonempty _
  let c := T.min' hT/2
  have hc : 0 < c := by
    dsimp [c]
    apply half_pos
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
    rw [← hp]
    exact hK _ _
  have hminor : ∀ x y, c ≤ K x y := by
    intro x y
    have hh := Finset.min'_le T (K x y) (Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩)
    have hm : 0 < T.min' hT := by change 0 < T.min' hT/2 at hc; linarith
    dsimp [c]
    linarith
  have hcard : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 ≤ 1-Fintype.card ι*c := by
    have hh := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hminor (Classical.arbitrary ι) y)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hrow] using sub_nonneg.mpr hh
  have hq1 : 1-Fintype.card ι*c < 1 := by nlinarith
  have hbound : ∀ k : ℕ, ∀ x, ∑ y, |(K^k) x y-μ y| ≤ 2*(1-Fintype.card ι*c)^k := by
    intro k
    induction k with
    | zero =>
      intro x
      simpa using kernel_row_l1_le_two (K := K^0) (kernel_pow_nonneg (fun x y => (hK x y).le) 0)
        hμ (kernel_pow_sum hrow 0) hmass x
    | succ k ih =>
      intro x
      simp only [pow_succ,Matrix.mul_apply]
      have hh := kernel_l1_contraction (p := fun y => (K^k) x y)
        ((kernel_pow_sum hrow k x).trans hmass.symm) hminor hrow hstat
      calc
        _ ≤ (1-Fintype.card ι*c)*(∑ y, |(K^k) x y-μ y|) := hh
        _ ≤ (1-Fintype.card ι*c)*(2*(1-Fintype.card ι*c)^k) := mul_le_mul_of_nonneg_left (ih x) hq0
        _ = _ := by ring
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/4 by norm_num))
  obtain ⟨k,hk⟩ := hh.exists
  refine ⟨k,?_⟩
  intro x
  have hb := hbound k x
  linarith

end KernelContraction

variable {n : ℕ} (W : Disorder n)

lemma discreteKernel_pos_of_sameExcept (hn : 0 < n) {i : Fin n} {x y : Spin n}
    (hxy : sameExcept i x y) : 0 < discreteKernel W x y := by
  have hi : 0 < siteKernel W i x y := by
    change 0 < if sameExcept i x y then gibbs W y/fiberMass W i x else 0
    rw [ite_eq_left hxy]
    exact div_pos (gibbs_pos W y) (fiberMass_pos W i x)
  have hs : 0 < ∑ j : Fin n, siteKernel W j x y :=
    lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => siteKernel_nonneg W j x y) (Finset.mem_univ i))
  change 0 < (n:ℝ)⁻¹*(∑ j : Fin n, siteKernel W j) x y
  simpa only [Matrix.sum_apply] using mul_pos (inv_pos.mpr (Nat.cast_pos.mpr hn)) hs

lemma discreteKernel_power_pos (hn : 0 < n) (x y : Spin n) : 0 < (discreteKernel W^n) x y := by
  classical
  let z (k : ℕ) : Spin n := fun i => if i.val < k then y i else x i
  have hh : ∀ k, k ≤ n → 0 < (discreteKernel W^k) x (z k) := by
    intro k
    induction k with
    | zero => intro _; simp [z]
    | succ k ih =>
      intro hk
      have hik : k < n := by omega
      have hstep : sameExcept ⟨k,hik⟩ (z k) (z (k+1)) := by
        intro j hj
        have hjk : j.val ≠ k := by intro he; apply hj; exact Fin.ext he
        dsimp [z]
        split_ifs <;> simp_all <;> omega
      rw [pow_succ,Matrix.mul_apply]
      exact lt_of_lt_of_le (mul_pos (ih (by omega)) (discreteKernel_pos_of_sameExcept W hn hstep))
        (Finset.single_le_sum (fun t _ => mul_nonneg
          (kernel_pow_nonneg (discreteKernel_nonneg W) k x t) (discreteKernel_nonneg W t (z (k+1))))
          (Finset.mem_univ (z k)))
  have hz : z n = y := by funext i; simp [z,i.isLt]
  simpa only [hz] using hh n le_rfl

lemma discrete_mixing_set_nonempty (hn : 0 < n) :
    {k : ℕ | ∀ x, discreteDistance W k x ≤ 1/4}.Nonempty := by
  obtain ⟨k,hk⟩ := strictly_positive_kernel_mixes (discreteKernel_power_pos W hn)
    (gibbs_nonneg W) (kernel_pow_sum (discreteKernel_sum W hn) n) (gibbs_sum W)
    (kernel_pow_stationary (discreteKernel_stationary W hn) n)
  refine ⟨n*k,?_⟩
  intro x
  simpa only [discreteDistance,totalVariation,pow_mul] using hk x

lemma continuousKernel_add (s t : ℝ) : continuousKernel W (s+t) = continuousKernel W s*continuousKernel W t := by
  unfold continuousKernel
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (generator W)).smul_left s).smul_right t)

lemma continuousKernel_nat (k : ℕ) : continuousKernel W k = continuousKernel W 1^k := by
  induction k with
  | zero => simp [continuousKernel]
  | succ k ih => rw [Nat.cast_add,Nat.cast_one,continuousKernel_add,ih,pow_succ]

lemma continuousKernel_one_pos (hn : 0 < n) (x y : Spin n) : 0 < continuousKernel W 1 x y := by
  rw [continuousKernel_poisson W hn]
  have hs := matrix_poisson_hasSum (discreteKernel W) ((n:ℝ)*1) x y
  have hle := sum_le_hasSum ({n} : Finset ℕ) (fun k _ => mul_nonneg (poisson_coeff_nonneg _ (by positivity) k)
    (kernel_pow_nonneg (discreteKernel_nonneg W) k x y)) hs
  simp only [Finset.sum_singleton] at hle
  have hp : 0 < (Real.exp (-((n:ℝ)*1))*((n:ℝ)*1)^n/n.factorial)*(discreteKernel W^n) x y := by
    exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (pow_pos (by positivity) n))
      (Nat.cast_pos.mpr (Nat.factorial_pos n))) (discreteKernel_power_pos W hn x y)
  exact hp.trans_le hle

lemma continuous_mixing_set_nonempty (hn : 0 < n) :
    {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ 1/4}.Nonempty := by
  obtain ⟨k,hk⟩ := strictly_positive_kernel_mixes (continuousKernel_one_pos W hn)
    (gibbs_nonneg W) (continuousKernel_sum W hn 1) (gibbs_sum W)
    (continuousKernel_stationary W hn 1)
  refine ⟨k,Nat.cast_nonneg k,?_⟩
  intro x
  simpa only [continuousDistance,totalVariation,continuousKernel_nat] using hk x

end

open Set Filter MeasureTheory

section MixingLower

variable {n : ℕ} (W : Disorder n)

lemma continuousDistance_antitone (hn : 0 < n) {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) (x : Spin n) :
    continuousDistance W t x ≤ continuousDistance W s x := by
  have hh := kernel_l1_contraction (p := continuousKernel W s x) (c := 0)
    ((continuousKernel_sum W hn s x).trans (gibbs_sum W).symm)
    (continuousKernel_nonneg W hn (t-s) (sub_nonneg.mpr hst))
    (continuousKernel_sum W hn (t-s)) (continuousKernel_stationary W hn (t-s))
  have he : continuousKernel W t = continuousKernel W s * continuousKernel W (t-s) := by
    rw [← continuousKernel_add]; congr 1; ring
  simp only [mul_zero,sub_zero,one_mul] at hh
  unfold continuousDistance totalVariation
  rw [he]
  simp only [Matrix.mul_apply]
  linarith

lemma discreteDistance_antitone (hn : 0 < n) {k l : ℕ} (hkl : k ≤ l) (x : Spin n) :
    discreteDistance W l x ≤ discreteDistance W k x := by
  have hh := kernel_l1_contraction (p := (discreteKernel W^k) x) (c := 0)
    ((kernel_pow_sum (discreteKernel_sum W hn) k x).trans (gibbs_sum W).symm)
    (kernel_pow_nonneg (discreteKernel_nonneg W) (l-k))
    (kernel_pow_sum (discreteKernel_sum W hn) (l-k))
    (kernel_pow_stationary (discreteKernel_stationary W hn) (l-k))
  have he : discreteKernel W^l = discreteKernel W^k*discreteKernel W^(l-k) := by
    rw [← pow_add,Nat.add_sub_of_le hkl]
  simp only [mul_zero,sub_zero,one_mul] at hh
  unfold discreteDistance totalVariation
  rw [he]
  simp only [Matrix.mul_apply]
  linarith

lemma continuousMixingTime_lower (hn : 0 < n) {t : ℝ} (h : 0 < continuousGoodMass W t) :
    t ≤ continuousMixingTime W := by
  apply le_csInf (continuous_mixing_set_nonempty W hn)
  intro s hs
  by_contra hst
  have hzero : continuousGoodMass W t = 0 := by
    unfold continuousGoodMass
    apply Finset.sum_eq_zero
    intro x _
    have hx := (continuousDistance_antitone W hn hs.1 (le_of_not_ge hst) x).trans (hs.2 x)
    rw [ite_eq_right (not_lt.mpr hx)]
  linarith

lemma discreteMixingTime_lower (hn : 0 < n) {k : ℕ} (h : 0 < discreteGoodMass W k) :
    k ≤ discreteMixingTime W := by
  have hs := Nat.sInf_mem (discrete_mixing_set_nonempty W hn)
  by_contra hk
  have hzero : discreteGoodMass W k = 0 := by
    unfold discreteGoodMass
    apply Finset.sum_eq_zero
    intro x _
    have hx := (discreteDistance_antitone W hn (le_of_not_ge hk) x).trans (hs x)
    rw [ite_eq_right (not_lt.mpr hx)]
  linarith

end MixingLower

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_HighTemperature
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators Topology
namespace CriticalSK


section

open Set Filter MeasureTheory ProbabilityTheory

lemma spinValue_abs (b : Bool) : |spinValue b|=1 := by cases b <;> norm_num [spinValue]

lemma hamiltonian_gaussianLinear {n : ℕ} (x : Spin n) (W : Disorder n) :
    hamiltonian W x = gaussianLinear (fun e : Edge n => spinValue (x e.val.1)*spinValue (x e.val.2)) W := by
  unfold hamiltonian gaussianLinear
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma edge_card_le_sq (n : ℕ) : Fintype.card (Edge n) ≤ n^2 := by
  simpa only [Edge,Fintype.card_prod,Fintype.card_fin,pow_two] using Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)

lemma hamiltonian_exp_moment {n : ℕ} (hn : 0<n) (x : Spin n) (a : ℝ) (ha : |a|=1) :
    Integrable (fun W : Disorder n => Real.exp (a*hamiltonian W x)) (disorderLaw n) ∧
    (∫ W : Disorder n, Real.exp (a*hamiltonian W x) ∂disorderLaw n) ≤ Real.exp ((n:ℝ)/2) := by
  let c := fun e : Edge n => a*(spinValue (x e.val.1)*spinValue (x e.val.2))
  have he (W : Disorder n) : a*hamiltonian W x = gaussianLinear c W := by
    rw [hamiltonian_gaussianLinear]
    simp only [gaussianLinear,Finset.mul_sum,c]
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp_rw [he]
  constructor
  · exact gaussian_exp_integrable _ c
  · change (∫ W, Real.exp (gaussianLinear c W) ∂gaussianScalarPi (n : ℝ≥0)⁻¹) ≤ _
    rw [gaussian_exp_integral]
    apply Real.exp_le_exp.mpr
    have hc (e : Edge n) : c e^2=1 := by
      have hh : |c e|=1 := by simp only [c,abs_mul,ha,spinValue_abs,mul_one]
      nlinarith [sq_abs (c e)]
    simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,NNReal.coe_inv,NNReal.coe_natCast]
    have hN : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hcard : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast edge_card_le_sq n
    have hh := mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hN.le)
    have hi : (n:ℝ)⁻¹*(n:ℝ)^2=(n:ℝ) := by field_simp
    rw [hi] at hh
    linarith

lemma hamiltonian_one_sided_tail {n : ℕ} (hn : 0<n) (x : Spin n) (a : ℝ) (ha : |a|=1) :
    (disorderLaw n).real {W | 3*(n:ℝ) ≤ a*hamiltonian W x} ≤ Real.exp (-(5/2:ℝ)*(n:ℝ)) := by
  obtain ⟨hi,hm⟩ := hamiltonian_exp_moment hn x a ha
  have hp := integral_dominates_event (E := {W : Disorder n | 3*(n:ℝ)≤a*hamiltonian W x})
    (hi.div_const (Real.exp (3*(n:ℝ)))) (fun W => div_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    (fun W hW => by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [one_mul] using Real.exp_le_exp.mpr hW)
  rw [integral_div] at hp
  apply hp.trans
  calc
    _ ≤ Real.exp ((n:ℝ)/2)/Real.exp (3*(n:ℝ)) := div_le_div_of_nonneg_right hm (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

lemma hamiltonian_abs_tail {n : ℕ} (hn : 0<n) (x : Spin n) :
    (disorderLaw n).real {W | 3*(n:ℝ) ≤ |hamiltonian W x|} ≤ 2*Real.exp (-(5/2:ℝ)*(n:ℝ)) := by
  have hs : {W : Disorder n | 3*(n:ℝ)≤|hamiltonian W x|} ⊆
      {W | 3*(n:ℝ)≤(1:ℝ)*hamiltonian W x} ∪ {W | 3*(n:ℝ)≤(-1:ℝ)*hamiltonian W x} := by
    intro W hW
    rcases le_abs.mp (show 3*(n:ℝ) ≤ |hamiltonian W x| from hW) with h|h
    · exact Or.inl (by dsimp; linarith)
    · exact Or.inr (by dsimp; linarith)
  have hp := (measureReal_mono (μ := disorderLaw n) hs).trans (measureReal_union_le _ _)
  have h1 := hamiltonian_one_sided_tail hn x 1 (by norm_num)
  have h2 := hamiltonian_one_sided_tail hn x (-1) (by norm_num)
  linarith

lemma spin_card_le_exp (n : ℕ) : (Fintype.card (Spin n):ℝ)≤Real.exp (n:ℝ) := by
  have h : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) h n
  rw [← Real.exp_nat_mul,mul_one] at hp
  simpa only [Spin,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using hp

lemma maximum_energy_tail {n : ℕ} (hn : 0<n) :
    (disorderLaw n).real {W | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|} ≤ 2*Real.exp (-(3/2:ℝ)*(n:ℝ)) := by
  have he : {W : Disorder n | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|} =
      ⋃ x : Spin n, {W | 3*(n:ℝ)≤|hamiltonian W x|} := by ext W; simp
  rw [he]
  calc
    _ ≤ ∑ x : Spin n, (disorderLaw n).real {W | 3*(n:ℝ)≤|hamiltonian W x|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : Spin n, 2*Real.exp (-(5/2:ℝ)*(n:ℝ)) := Finset.sum_le_sum (fun x _ => hamiltonian_abs_tail hn x)
    _ = (Fintype.card (Spin n):ℝ)*(2*Real.exp (-(5/2:ℝ)*(n:ℝ))) := by simp
    _ ≤ Real.exp (n:ℝ)*(2*Real.exp (-(5/2:ℝ)*(n:ℝ))) := mul_le_mul_of_nonneg_right (spin_card_le_exp n) (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm _ 2,mul_assoc,← Real.exp_add]; congr 2; ring

end

section

open Set Filter MeasureTheory

lemma polynomial_exp_eventually_le (C : ℝ) {a : ℝ} (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^2 ≤ Real.exp (a*(n:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => C*((n:ℝ)^2*Real.exp (-a*(n:ℝ)))) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa only [Function.comp_def,Real.rpow_two,mul_zero] using hh
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  have hm := mul_le_mul_of_nonneg_right hn.le (Real.exp_nonneg (a*(n:ℝ)))
  have he : Real.exp (-a*(n:ℝ))*Real.exp (a*(n:ℝ))=1 := by
    rw [← Real.exp_add,show -a*(n:ℝ)+a*(n:ℝ)=0 by ring,Real.exp_zero]
  simpa only [one_mul,mul_assoc,he,mul_one] using hm

lemma finite_tempered_mixing {n : ℕ} (hn : 0<n) (W : Disorder n) {β C : ℝ}
    (hβ : β≤1) (hC : 1≤C) (hH : ∀ x, |hamiltonian W x|≤3*(n:ℝ))
    (hgap : ∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f) :
    continuousMixingTime W ≤ 44*C*(n:ℝ)^2*Real.exp (6*(1-β)*(n:ℝ)) ∧
    (discreteMixingTime W:ℝ) ≤ 44*C*(n:ℝ)^2*Real.exp (6*(1-β)*(n:ℝ)) := by
  have hN : (1:ℝ)≤n := by exact_mod_cast hn
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hE : 1≤Real.exp (6*(1-β)*(n:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hg (f : Spin n → ℝ) : variance W f ≤ (C*Real.exp (6*(1-β)*(n:ℝ)))*dirichlet W f := by
    convert poincare_temperature_comparison W hβ hCp.le hH hgap f using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    ring
  have hb := finite_gap_mixing_bounds W hn (by nlinarith : 1≤C*Real.exp (6*(1-β)*(n:ℝ)))
    (by positivity : (0:ℝ)≤3*(n:ℝ)) hg hH
  have hN2 : (n:ℝ)≤(n:ℝ)^2 := by nlinarith
  have hP : 0 ≤ C*Real.exp (6*(1-β)*(n:ℝ)) := by positivity
  constructor
  · refine hb.1.trans ?_
    have hh := mul_le_mul_of_nonneg_right (show 4*(2*(3*(n:ℝ))+(n:ℝ)+4) ≤ 44*(n:ℝ)^2 by nlinarith) hP
    nlinarith only [hh]
  · refine hb.2.trans ?_
    have hh := mul_le_mul_of_nonneg_right (show (n:ℝ)*(2*(3*(n:ℝ))+(n:ℝ)+4)+1 ≤ 44*(n:ℝ)^2 by nlinarith) hP
    have hc : 1≤C*Real.exp (6*(1-β)*(n:ℝ)) := by nlinarith
    nlinarith only [hh,hc]

lemma tempered_mixing_eventual_implication {ε β C : ℝ} (hε : 0<ε) (hβ : β≤1)
    (hsmall : 6*(1-β) ≤ ε/2) (hC : 1≤C) :
    ∀ᶠ n : ℕ in atTop, ∀ W : Disorder n,
      (∀ x, |hamiltonian W x|≤3*(n:ℝ)) →
      (∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f) →
      continuousMixingTime W ≤ Real.exp (ε*(n:ℝ)) ∧
      (discreteMixingTime W:ℝ) ≤ Real.exp (ε*(n:ℝ)) := by
  filter_upwards [eventually_gt_atTop (0:ℕ),polynomial_exp_eventually_le (44*C) (by positivity : 0<ε/2)] with n hn hp W hH hg
  have hb := finite_tempered_mixing hn W hβ hC hH hg
  have hh : 44*C*(n:ℝ)^2*Real.exp (6*(1-β)*(n:ℝ)) ≤ Real.exp (ε*(n:ℝ)) := by
    calc
      _ ≤ Real.exp ((ε/2)*(n:ℝ))*Real.exp (6*(1-β)*(n:ℝ)) := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = Real.exp ((ε/2)*(n:ℝ)+6*(1-β)*(n:ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)])
  exact ⟨hb.1.trans hh,hb.2.trans hh⟩

lemma temperature_close_to_one {ε : ℝ} (hε : 0<ε) : ∃ β : ℝ, 0<β ∧ β<1 ∧ 6*(1-β)≤ε/2 := by
  let δ := min (ε/12) (1/2)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ≤1/2 := min_le_right _ _
  have hδε : δ≤ε/12 := min_le_left _ _
  refine ⟨1-δ,by linarith,by linarith,?_⟩
  linarith

end

open Set Filter MeasureTheory

lemma fiberMass_continuous {n : ℕ} (i : Fin n) (x : Spin n) :
    Continuous (fun W : Disorder n => fiberMass W i x) := by
  unfold fiberMass
  apply continuous_finsetSum
  intro y _
  by_cases hy : sameExcept i x y
  · simp only [ite_eq_left hy]; exact gibbs_continuous y
  · simp only [ite_eq_right hy]; exact continuous_const

lemma siteKernel_continuous {n : ℕ} (i : Fin n) (x y : Spin n) :
    Continuous (fun W : Disorder n => siteKernel W i x y) := by
  by_cases h : sameExcept i x y
  · simp only [siteKernel,ite_eq_left h]
    exact (gibbs_continuous y).div (fiberMass_continuous i x) (fun W => (fiberMass_pos W i x).ne')
  · simp only [siteKernel,ite_eq_right h]; exact continuous_const

lemma mean_continuous {n : ℕ} (f : Spin n → ℝ) : Continuous (fun W : Disorder n => mean W f) := by
  unfold mean
  exact continuous_finsetSum _ (fun x _ => (gibbs_continuous x).mul continuous_const)

lemma variance_continuous {n : ℕ} (f : Spin n → ℝ) : Continuous (fun W : Disorder n => variance W f) := by
  unfold variance
  change Continuous (fun W : Disorder n => ∑ x, gibbs W x*(f x-mean W f)^2)
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul ((continuous_const.sub (mean_continuous f)).pow 2)

lemma dirichlet_continuous {n : ℕ} (f : Spin n → ℝ) : Continuous (fun W : Disorder n => dirichlet W f) := by
  unfold dirichlet mean
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  apply (gibbs_continuous x).mul
  apply Continuous.pow
  apply continuous_const.sub
  exact continuous_finsetSum _ (fun y _ => (siteKernel_continuous i x y).mul continuous_const)

lemma poincareEvent_closed (n : ℕ) (β C : ℝ) : IsClosed (poincareEvent n β C) := by
  have he : poincareEvent n β C = ⋂ f : Spin n → ℝ,
      {W : Disorder n | variance (β • W) f ≤ C*dirichlet (β • W) f} := by ext W; simp [poincareEvent]
  rw [he]
  apply isClosed_iInter
  intro f
  have hs : Continuous (fun W : Disorder n => β • W) := continuous_const_smul β
  exact isClosed_le ((variance_continuous f).comp hs)
    (continuous_const.mul ((dirichlet_continuous f).comp hs))

lemma mixingReductionError_tendsto {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => mixingReductionError n ε) atTop (𝓝 0) := by
  have hc := realized_continuous_initial_states (fun n => (n:ℝ)^(2/3-ε))
    (fun _ => by positivity) (rpow_ratio_tendsto_zero hε) 1 zero_lt_one
  have hd := realized_discrete_initial_states (fun n => ⌈(n:ℝ)^(5/3-ε)⌉₊)
    (ceil_rpow_ratio_tendsto_zero (by norm_num : (0:ℝ)<5/3) hε) 1 zero_lt_one
  have he : Tendsto (fun n : ℕ => 2*Real.exp (-(3/2:ℝ)*(n:ℝ))) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => -(3/2:ℝ)*(n:ℝ)) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by norm_num : -(3/2:ℝ)<0)).mpr tendsto_natCast_atTop_atTop
    simpa using (Real.tendsto_exp_atBot.comp ht).const_mul 2
  simpa only [mixingReductionError,add_zero] using (he.add hc).add hd

lemma mixingGapReduction_lower {ε β C : ℝ} (hε : 0<ε) (hβ : β≤1)
    (hsmall : 6*(1-β)≤ε/2) (hC : 1≤C) :
    ∀ᶠ n : ℕ in atTop,
      (disorderLaw n).real (poincareEvent n β C)-mixingReductionError n ε ≤
        (disorderLaw n).real (twoClockMixingEvent n ε) := by
  filter_upwards [tempered_mixing_eventual_implication hε hβ hsmall hC,
    eventually_gt_atTop (0:ℕ)] with n hn hnp
  let B : Set (Disorder n) := {W | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|}
  let Lc : Set (Disorder n) := {W | (1:ℝ)≤|continuousGoodMass W ((n:ℝ)^(2/3-ε))-1|}
  let Ld : Set (Disorder n) := {W | (1:ℝ)≤|discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊-1|}
  have hs : poincareEvent n β C ⊆ ((twoClockMixingEvent n ε ∪ B) ∪ Lc) ∪ Ld := by
    intro W hW
    by_cases hb : W∈B
    · exact Or.inl (Or.inl (Or.inr hb))
    by_cases hc : W∈Lc
    · exact Or.inl (Or.inr hc)
    by_cases hd : W∈Ld
    · exact Or.inr hd
    apply Or.inl ∘ Or.inl ∘ Or.inl
    have hH : ∀ x, |hamiltonian W x|≤3*(n:ℝ) := by
      intro x
      by_contra hx
      exact hb ⟨x,(lt_of_not_ge hx).le⟩
    have hu := hn W hH hW
    have hc' : 0 < continuousGoodMass W ((n:ℝ)^(2/3-ε)) := by
      have hh : |continuousGoodMass W ((n:ℝ)^(2/3-ε))-1|<1 := lt_of_not_ge hc
      have hl := (abs_lt.mp hh).1
      linarith
    have hd' : 0<discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊ := by
      have hh : |discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊-1|<1 := lt_of_not_ge hd
      have hl := (abs_lt.mp hh).1
      linarith
    exact ⟨continuousMixingTime_lower W hnp hc',hu.1,
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (discreteMixingTime_lower W hnp hd')),hu.2⟩
  have hp := measureReal_mono (μ := disorderLaw n) hs
  have h1 := measureReal_union_le (μ := disorderLaw n) ((twoClockMixingEvent n ε ∪ B) ∪ Lc) Ld
  have h2 := measureReal_union_le (μ := disorderLaw n) (twoClockMixingEvent n ε ∪ B) Lc
  have h3 := measureReal_union_le (μ := disorderLaw n) (twoClockMixingEvent n ε) B
  have hb := maximum_energy_tail hnp
  change (disorderLaw n).real B ≤ _ at hb
  change (disorderLaw n).real (poincareEvent n β C)-
    (2*Real.exp (-(3/2:ℝ)*(n:ℝ))+(disorderLaw n).real Lc+(disorderLaw n).real Ld) ≤ _
  linarith

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Rayleigh
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

@[simp] lemma abs_spinValue (b : Bool) : |spinValue b| = 1 := by cases b <;> norm_num [spinValue]

end

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_FiniteSpinCalculus
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

theorem coupling_symm (g : Disorder n) (i k : Fin n) : coupling g i k = coupling g k i := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · simp [coupling, hik, not_lt_of_gt hik]
  · rfl
  · simp [coupling, hki, not_lt_of_gt hki]

end FiniteSpinCalculus

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalMixing_Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

lemma disorderLaw_temperature_map (n : ℕ) (β : ℝ) :
    (disorderLaw n).map (fun W => β • W) = SKGap.disorderLaw β n := by
  unfold disorderLaw SKGap.disorderLaw
  change (Measure.pi (fun _ : Edge n => gaussianReal 0 (n : ℝ≥0)⁻¹)).map
      (fun W e => β * W e) = _
  rw [Measure.pi_map_pi (f := fun _ : Edge n => fun a : ℝ => β * a)
    (fun _ => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  funext e
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_natCast]
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg β) (Nat.cast_nonneg n))]
  exact (div_eq_mul_inv _ _).symm

lemma companion_hamiltonian {n : ℕ} (W : Disorder n) (x : Spin n) :
    SKGap.hamiltonian W 0 x = hamiltonian W x := by
  unfold SKGap.hamiltonian
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [symmetric_sum_upper _ (by
    intro i j
    rw [SKGap.coupling_symm W i j]
    ring)]
  have hd : (∑ i : Fin n, SKGap.spinValue (x i) * SKGap.coupling W i i *
      SKGap.spinValue (x i)) = 0 := by simp [SKGap.coupling_diag]
  rw [hd, zero_add]
  have he : (∑ e : Edge n, SKGap.spinValue (x e.val.1) *
      SKGap.coupling W e.val.1 e.val.2 * SKGap.spinValue (x e.val.2)) = hamiltonian W x := by
    unfold hamiltonian
    apply Finset.sum_congr rfl
    intro e _
    simp only [SKGap.coupling, dite_eq_left e.property]
    change spinValue (x e.val.1) * W e * spinValue (x e.val.2) = _
    ring
  rw [he]
  ring

lemma companion_partition {n : ℕ} (W : Disorder n) : SKGap.partition W 0 = partition W := by
  simp only [SKGap.partition, SKGap.weight, companion_hamiltonian, partition]

lemma companion_mass {n : ℕ} (W : Disorder n) (x : Spin n) :
    SKGap.mass W 0 x = gibbs W x := by
  rw [SKGap.mass, SKGap.weight, companion_hamiltonian, companion_partition]
  rfl

lemma companion_expectation {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) :
    SKGap.expectation W 0 f = mean W f := by
  simp only [SKGap.expectation, companion_mass, mean]

lemma companion_variance {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) :
    SKGap.variance W 0 f = variance W f := by
  simp only [SKGap.variance, companion_expectation, variance]

lemma companion_conditionalExpectation {n : ℕ} (W : Disorder n) (i : Fin n)
    (f : Spin n → ℝ) (x : Spin n) :
    SKGap.conditionalExpectation W 0 i f x = ∑ y, siteKernel W i x y * f y := by
  rw [← siteAverage_eq, siteAverage_two]
  rw [← companion_mass W x, show flipSite i x = SKGap.flip i x from rfl,
    ← companion_mass W (SKGap.flip i x)]
  simp only [SKGap.conditionalExpectation, SKGap.mass, div_mul_eq_mul_div, ← add_div,
    div_div_div_cancel_right₀ (ne_of_gt (SKGap.partition_pos W 0))]

lemma companion_dirichlet {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) :
    SKGap.dirichlet W 0 f = dirichlet W f := by
  simp only [SKGap.dirichlet, companion_expectation, companion_conditionalExpectation, dirichlet]

lemma companion_poincare_preimage (n : ℕ) (β C : ℝ) :
    (fun W : Disorder n => β • W) ⁻¹' SKGap.poincareEvent n C = poincareEvent n β C := by
  ext W
  simp only [Set.mem_preimage, SKGap.poincareEvent, poincareEvent, Set.mem_ofPred_eq,
    companion_variance, companion_dirichlet]

lemma companion_poincare_measurable (n : ℕ) (C : ℝ) :
    MeasurableSet (SKGap.poincareEvent n C) := by
  have he : SKGap.poincareEvent n C = poincareEvent n 1 C := by
    simpa only [one_smul, Set.preimage_id'] using companion_poincare_preimage n 1 C
  rw [he]
  exact (poincareEvent_closed n 1 C).measurableSet

lemma companion_poincare_probability (n : ℕ) (β C : ℝ) :
    SKGap.disorderLaw β n (SKGap.poincareEvent n C) = disorderLaw n (poincareEvent n β C) := by
  rw [← disorderLaw_temperature_map,
    Measure.map_apply (continuous_const_smul β).measurable (companion_poincare_measurable n C),
    companion_poincare_preimage]

theorem fixed_temperature_poincare (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ Tendsto (fun n : ℕ =>
      (disorderLaw n).real (poincareEvent n β C)) atTop (𝓝 1) := by
  obtain ⟨C, hC, hP, _⟩ := SKGap.sk_main β hβ0 hβ1
  have hp : Tendsto (fun n : ℕ => (disorderLaw n).real (poincareEvent n β C))
      atTop (𝓝 1) := by
    simp_rw [companion_poincare_probability] at hP
    simpa only [Measure.real, ENNReal.toReal_one, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hP
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds
  · intro n
    refine measureReal_mono ?_
    intro W hW f
    exact (hW f).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (dirichlet_nonneg (β • W) f))
  · intro n
    exact measureReal_le_one

end CriticalSK
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalMixing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

theorem critical_two_clock_mixing_s2_oai (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (disorderLaw n).real (twoClockMixingEvent n ε))
      atTop (𝓝 1) := by
  obtain ⟨β, hβ0, hβ1, hsmall⟩ := temperature_close_to_one hε
  obtain ⟨C, hC, hP⟩ := fixed_temperature_poincare β hβ0 hβ1
  have hl : Tendsto (fun n : ℕ => (disorderLaw n).real (poincareEvent n β C) -
      mixingReductionError n ε) atTop (𝓝 1) := by
    simpa only [sub_zero] using hP.sub (mixingReductionError_tendsto hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    (mixingGapReduction_lower hε hβ1.le hsmall hC)
    (Filter.Eventually.of_forall (fun _ => measureReal_le_one))

end CriticalSK
end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.critical_two_clock_mixing_s2_oai := @OAI.CriticalSK.critical_two_clock_mixing_s2_oai
