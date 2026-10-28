-- Prove2me | solution 1 for OAI.CriticalSK.critical_mixing_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:50.66968+00:00
-- url     : https://prove2.me/submissions/ca66e606-71ea-4584-be64-638ac73f8286

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK000
import Theorems.Thm_OAI_CriticalSK_natural_smallBall_tight

section
-- module Solutions.OAIQW_CriticalSK.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434


end OAI.CriticalSK
end

section
-- module Solutions.OAIQW_CriticalSK.Gibbs
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.HeatBath
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.Equilibrium
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
-- module Solutions.OAIQW_CriticalSK.Mixing
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

lemma event_probability_one_of_error_zero {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (E B : ∀ n, Set (X n)) (hcover : ∀ᶠ n : ℕ in atTop, E n ∪ B n = univ)
    (hB : Tendsto (fun n => (μ n).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real (E n)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hcover,hB.eventually (gt_mem_nhds (show 0 < 1-a by linarith))] with n hn hnb
    have hh := measureReal_union_le (μ := μ n) (E n) (B n)
    rw [hn,probReal_univ] at hh
    linarith
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

lemma continuousMixingTime_lower_limit (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hscale : Tendsto (fun n => t n/(n:ℝ)^(2/3:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (disorderLaw n).real {W | t n ≤ continuousMixingTime W}) atTop (𝓝 1) := by
  apply event_probability_one_of_error_zero (μ := disorderLaw)
    (B := fun n => {W | (1:ℝ) ≤ |continuousGoodMass W (t n)-1|})
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply Set.eq_univ_of_forall
    intro W
    by_cases hW : 0 < continuousGoodMass W (t n)
    · exact Or.inl (continuousMixingTime_lower W hn hW)
    · exact Or.inr (by change (1:ℝ) ≤ |continuousGoodMass W (t n)-1|; rw [abs_of_nonpos (by linarith [continuousGoodMass_le_one W (t n)])]; linarith)
  · exact realized_continuous_initial_states t ht hscale 1 zero_lt_one

lemma discreteMixingTime_lower_limit (k : ℕ → ℕ)
    (hscale : Tendsto (fun n => (k n:ℝ)/(n:ℝ)^(5/3:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (disorderLaw n).real {W | k n ≤ discreteMixingTime W}) atTop (𝓝 1) := by
  apply event_probability_one_of_error_zero (μ := disorderLaw)
    (B := fun n => {W | (1:ℝ) ≤ |discreteGoodMass W (k n)-1|})
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply Set.eq_univ_of_forall
    intro W
    by_cases hW : 0 < discreteGoodMass W (k n)
    · exact Or.inl (discreteMixingTime_lower W hn hW)
    · exact Or.inr (by change (1:ℝ) ≤ |discreteGoodMass W (k n)-1|; rw [abs_of_nonpos (by linarith [discreteGoodMass_le_one W (k n)])]; linarith)
  · exact realized_discrete_initial_states k hscale 1 zero_lt_one

theorem critical_mixing_lower_bounds_oai (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (disorderLaw n).real {W | (n:ℝ)^(2/3-ε) ≤ continuousMixingTime W}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real {W | (n:ℝ)^(5/3-ε) ≤ (discreteMixingTime W:ℝ)}) atTop (𝓝 1) := by
  constructor
  · exact continuousMixingTime_lower_limit (fun n => (n:ℝ)^(2/3-ε)) (fun _ => by positivity) (rpow_ratio_tendsto_zero hε)
  · have hh := discreteMixingTime_lower_limit (fun n => ⌈(n:ℝ)^(5/3-ε)⌉₊)
      (ceil_rpow_ratio_tendsto_zero (by norm_num : (0:ℝ) < 5/3) hε)
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [(tendsto_order.mp hh).1 a ha] with n hn
      refine lt_of_lt_of_le hn (measureReal_mono ?_)
      intro W hW
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hW)
    · intro a ha
      exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.critical_mixing_lower_bounds_oai := @OAI.CriticalSK.critical_mixing_lower_bounds_oai
