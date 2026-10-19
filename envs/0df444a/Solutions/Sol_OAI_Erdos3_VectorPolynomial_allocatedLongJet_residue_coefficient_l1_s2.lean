-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_l1_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:29:28.180983+00:00
-- url     : https://prove2.me/submissions/f22eb0f9-d46e-4c64-bde9-4656b6b61909

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernelDensity_bounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiniteLongJet_l1_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedKernel_replacement_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerKernelDensity_bounds_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem coordinateMatrix_entry_le_norm (f : (J → ℝ) →L[ℝ] (I → ℝ)) (i : I) (j : J) :
    |(LinearMap.toMatrix' f.toLinearMap) i j| ≤ ‖f‖ := by
  rw [LinearMap.toMatrix'_apply]
  calc
    |f (Pi.single j 1) i| ≤ ‖f (Pi.single j 1)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f (Pi.single j 1)) i
    _ ≤ ‖f‖ * ‖(Pi.single j 1 : J → ℝ)‖ := f.le_opNorm (Pi.single j 1)
    _ = ‖f‖ := by rw [Pi.norm_single, norm_one, mul_one]

theorem inverseJacobian_le_norm_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {U : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ U) :
    inverseJacobian A ≤ (Fintype.card I).factorial * U ^ Fintype.card I := by
  have h := matrix_det_abs_le_uniform_bound
    (LinearMap.toMatrix' A.symm.toContinuousLinearMap.toLinearMap)
    (fun i j => (coordinateMatrix_entry_le_norm A.symm.toContinuousLinearMap i j).trans hA)
  rw [LinearMap.det_toMatrix'] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

theorem polynomialC2BoxBudget_dominates (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (d + 1 : ℝ) ^ N * C ≤ polynomialC2BoxBudget N d C ∧
      N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) ≤ polynomialC2BoxBudget N d C ∧
      N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) ≤ polynomialC2BoxBudget N d C := by
  let x : ℝ := (N : ℝ) * d
  let a : ℝ := (d + 1 : ℝ) ^ N * C
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h0 : 1 ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have h1 : x ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have h2 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
  have hb : polynomialC2BoxBudget N d C = (1 + x) ^ 2 * a := by dsimp [polynomialC2BoxBudget, x, a]; ring
  rw [hb]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0 ha
  · have he : N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) = x * a := by dsimp [x, a]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h1 ha
  · have he : N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) = x ^ 2 * a := by
      dsimp [x, a]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h2 ha

end Erdos3

end

section

namespace Erdos3

theorem polynomialC2BoxBudget_le_exp (N d : ℕ) {C p : ℝ} (hC : 0 ≤ C) (hCp : C ≤ Real.exp p) :
    polynomialC2BoxBudget N d C ≤ Real.exp (3 * (N : ℝ) * d + p) := by
  have hbase : 1 + (N : ℝ) * d ≤ Real.exp ((N : ℝ) * d) := by
    simpa only [add_comm] using Real.add_one_le_exp ((N : ℝ) * d)
  have hdegree : (d + 1 : ℝ) ≤ Real.exp (d : ℝ) := Real.add_one_le_exp _
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (N : ℝ) * d) hbase 2
  have hterms := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d + 1 : ℝ)) hdegree N
  calc
    _ ≤ (Real.exp ((N : ℝ) * d)) ^ 2 * (Real.exp (d : ℝ)) ^ N * Real.exp p :=
      mul_le_mul (mul_le_mul hpow hterms (by positivity) (by positivity)) hCp hC (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI


namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetAllowances
namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_pos (q h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetInterpolationAllowance q h κ := by
  unfold kernelJetInterpolationAllowance
  positivity

theorem kernelJetEntryAllowance_pos (q h : ℕ) : 0 < kernelJetEntryAllowance q h := by
  unfold kernelJetEntryAllowance
  positivity

theorem kernelJetMinorThreshold_pos (q n j h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetMinorThreshold q n j h κ := by
  have := kernelJetInterpolationAllowance_pos q h hκ
  unfold kernelJetMinorThreshold
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3

theorem normalizedIntegerColumns_submatrix {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ) (p : I → J) :
    (normalizedIntegerColumns A S P).submatrix id p =
      normalizedIntegerPivot (A.submatrix id p) (fun i => S (p i)) P := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, normalizedIntegerColumns_entry_div,
    normalizedIntegerPivot_entry]


open scoped Matrix

theorem normalized_remainingMatrixColumns {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P =
      remainingMatrixColumns (normalizedIntegerColumns A S P) s := by
  classical
  ext i j
  simp only [remainingMatrixColumns, Matrix.submatrix_apply, id_eq,
    normalizedIntegerColumns_entry_div]

end Erdos3


namespace Erdos3

theorem normalizedScalarKernelJet_eq {I J O : Type*}
    [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) =
      normalizedScalarKernelJet x h rows :=
  normalizedBoundedIntegerJetMatrix_eq _ _ _ _ _ hH

theorem normalized_scalarKernel_pivot {I J O : Type*} [DecidableEq I] [Fintype J]
    [Fintype O] [DecidableEq O] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) (p : O → BoundedIntegerExponent J h)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
      (fun o => kernelJetCoefficientScale J h L H (p o)) (fun _ => H) =
      (normalizedScalarKernelJet x h rows).submatrix id p := by
  have he := congrArg (fun A : Matrix O (BoundedIntegerExponent J h) ℝ => A.submatrix id p)
    (normalizedScalarKernelJet_eq x h rows hH)
  rw [normalizedIntegerColumns_submatrix] at he
  exact he

theorem scalarKernel_pivot_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0)
    {H : ℝ} (hH : 0 < H) :
    normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L H (s i))
      (fun _ => H) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) hH (s i))
      (fun _ => hH) = scalarKernelFixedPivot hL x degree rows s hs := by
  ext v i
  change ((normalizedPivotEquiv _ hs _ _ _ _).toContinuousLinearMap v) i =
    ((scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap v) i
  simp only [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
    normalized_scalarKernel_pivot x degree rows s hH.ne',
    normalized_scalarKernel_pivot x degree rows s one_ne_zero]

theorem scalarKernel_free_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    {H : ℝ} (hH : H ≠ 0) :
    matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x degree rows) s)
      (fun j => kernelJetCoefficientScale J degree L H j.val) (fun _ => H)) =
      scalarKernelFixedFree x degree rows s := by
  rw [normalized_remainingMatrixColumns]
  unfold scalarKernelFixedFree
  apply congrArg matrixSupCLM
  ext i j
  change normalizedIntegerColumns (scalarKernelIntegerJet x degree rows)
    (kernelJetCoefficientScale J degree L H) (fun _ => H) i j.val =
      normalizedScalarKernelJet x degree rows i j.val
  have he := congrFun (congrFun (normalizedScalarKernelJet_eq x degree rows hH) i) j.val
  simpa only [normalizedIntegerColumns_entry_div, kernelJetCoefficientScale] using he

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JetOutputRadiusLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem polynomialBoxLip_le_exp (n d : ℕ) (C : ℝ≥0) {p : ℝ} (hC : (C : ℝ) ≤ Real.exp p) :
    (polynomialBoxLip n d C : ℝ) ≤ Real.exp (3*(n : ℝ)*d+p) := by
  have h := (polynomialC2BoxBudget_dominates n d C.coe_nonneg).2.1
  have h' : (polynomialBoxLip n d C : ℝ) ≤ polynomialC2BoxBudget n d C := h
  exact h'.trans (polynomialC2BoxBudget_le_exp n d C.coe_nonneg hC)

theorem normalizedJetMass_le_exp (α : Type*) [Fintype α] (d : ℕ) :
    (normalizedJetMass α d : ℝ) ≤ Real.exp ((Fintype.card α : ℝ)*(d+1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1
    norm_num
  have hbase := Real.add_one_le_exp (Fintype.card α : ℝ)
  change (2 : ℝ)^Fintype.card α * ((Fintype.card α : ℝ)+1)^d ≤ _
  calc
    _ ≤ (Real.exp 1)^Fintype.card α * (Real.exp (Fintype.card α : ℝ))^d :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) htwo _) (pow_le_pow_left₀ (by positivity) hbase _)
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem normalizedJetColumnLip_le_exp (α : Type*) [Fintype α] (n p d : ℕ) :
    (n : ℝ) * polynomialBoxLip p d (normalizedJetMass α d) ≤
      Real.exp (n + 3*(p : ℝ)*d + (Fintype.card α : ℝ)*(d+1)) := by
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    _ ≤ Real.exp (n : ℝ) * Real.exp (3*(p : ℝ)*d + (Fintype.card α : ℝ)*(d+1)) :=
      mul_le_mul hn (polynomialBoxLip_le_exp p d _ (normalizedJetMass_le_exp α d))
        (NNReal.coe_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem jetOutputRadiusLog_nonneg (q n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ jetOutputRadiusLog q n d P := by unfold jetOutputRadiusLog; positivity

theorem normalizedJetOutputRadius_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (α N : Type*) [Fintype α] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) {P : ℝ} (hP : 0 ≤ P)
    (hA : ‖A.toContinuousLinearMap‖ ≤ Real.exp P) (hF : ‖F‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hS : (S : ℝ) ≤ Real.exp P) :
    (normalizedJetOutputRadius α N A F degree R S : ℝ) ≤
      Real.exp (jetOutputRadiusLog (Fintype.card α) (Fintype.card N) degree P) := by
  have hAF := add_le_exp_add_one hP hP hA hF
  have hlinear : (‖A.toContinuousLinearMap‖+‖F‖)*(R : ℝ) ≤ Real.exp (3*P+1) := by
    calc
      _ ≤ Real.exp (P+P+1)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmass : (normalizedJetMass α degree : ℝ) ≤
      Real.exp (Fintype.card α+(degree : ℝ)*Fintype.card α) := by
    have he : (Fintype.card α : ℝ)*(degree+1) = Fintype.card α+(degree : ℝ)*Fintype.card α := by ring
    simpa only [he] using normalizedJetMass_le_exp α degree
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  have htail : (Fintype.card N : ℝ)*(normalizedJetMass α degree : ℝ)*(S : ℝ) ≤
      Real.exp (Fintype.card N+Fintype.card α+(degree : ℝ)*Fintype.card α+P) := by
    calc
      _ ≤ Real.exp (Fintype.card N : ℝ)*Real.exp (Fintype.card α+(degree : ℝ)*Fintype.card α)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ 3*P+1 by positivity)
    (show 0 ≤ (Fintype.card N : ℝ)+Fintype.card α+(degree : ℝ)*Fintype.card α+P by positivity) hlinear htail
  change (‖A.toContinuousLinearMap‖+‖F‖)*(R : ℝ)+
    (Fintype.card N : ℝ)*(normalizedJetMass α degree : ℝ)*(S : ℝ) ≤ _
  apply hs.trans_eq
  congr 1
  unfold jetOutputRadiusLog
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem profileWidthPower_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (hi : δ⁻¹ ≤ Real.exp t) : δ⁻¹ ^ n ≤ Real.exp ((n : ℝ) * t) := by
  calc
    _ ≤ (Real.exp t)^n := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem affineProductProfileLip_le_exp (I : Type*) [Fintype I]
    {δ : ℝ≥0} {t : ℝ} (hi : (δ : ℝ)⁻¹ ≤ Real.exp t) :
    (affineProductProfileLip I δ : ℝ) ≤ Real.exp (affineProfileLogBound (Fintype.card I) t) := by
  have hn : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_inv]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp (probabilityProfileLipschitz : ℝ) *
        (Real.exp t)^(Fintype.card I + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [affineProfileLogBound, Nat.cast_add, Nat.cast_one]

theorem affineProductProfile_cap_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) (hi : δ⁻¹ ≤ Real.exp t) :
    δ⁻¹ ^ n ≤ Real.exp (affineProfileLogBound n t) := by
  apply (profileWidthPower_le_exp n hδ hi).trans
  apply Real.exp_le_exp.mpr
  unfold affineProfileLogBound
  nlinarith [NNReal.coe_nonneg probabilityProfileLipschitz, Nat.cast_nonneg n (α := ℝ)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem inverseJacobian_le_exp {I : Type*} [Fintype I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {P : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P) :
    inverseJacobian A ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P) := by
  classical
  apply (inverseJacobian_le_norm_bound A hA).trans
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2)*(Real.exp P)^Fintype.card I := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem pivotKernelCap_le_exp {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R H : ℝ≥0) {P Q : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hH : (H : ℝ) ≤ Real.exp Q) :
    (pivotKernelCap J A R H : ℝ) ≤
      Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P+Q+Fintype.card J*(P+1)) := by
  have hJ := inverseJacobian_le_exp A hA
  have hJ0 := (inverseJacobian_pos A).le
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2R : 2*(R : ℝ) ≤ Real.exp (P+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  change inverseJacobian A*(H : ℝ)*(2*(R : ℝ))^Fintype.card J ≤ _
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P)*Real.exp Q*
        (Real.exp (P+1))^Fintype.card J := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]

theorem pivotKernelLip_le_exp {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R K : ℝ≥0) {P Q : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (pivotKernelLip J A R K : ℝ) ≤
      Real.exp ((Fintype.card I : ℝ)^2+(Fintype.card I+1)*P+Q+Fintype.card J*(P+1)) := by
  have hcap := pivotKernelCap_le_exp J A R K hA hR hK
  change (pivotKernelCap J A R K : ℝ)*‖A.symm.toContinuousLinearMap‖ ≤ _
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P+Q+Fintype.card J*(P+1))*Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem masked_product_error {D : Type*} [Fintype D]
    (a f m : D → ℝ) {C G ε : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hf : ∀ d, |f d| ≤ C) (hm : ∀ d, |m d| ≤ G)
    (he : ∀ d, |a d-m d*f d| ≤ ε) :
    |(∏ d, a d) - (∏ d, m d)*(∏ d, f d)| ≤
      Fintype.card D * ε * (1+G*C+ε)^Fintype.card D := by
  have hb : 1 ≤ 1+G*C+ε := by nlinarith [mul_nonneg hG hC]
  have hmf (d) : |m d*f d| ≤ G*C := by
    rw [abs_mul]
    exact mul_le_mul (hm d) (hf d) (abs_nonneg _) hG
  have ha (d) : |a d| ≤ 1+G*C+ε := by
    have ht := abs_add_le (a d-m d*f d) (m d*f d)
    rw [sub_add_cancel] at ht
    linarith [he d, hmf d]
  simpa only [Finset.card_univ, Finset.prod_mul_distrib] using
    abs_finset_prod_sub_prod_le Finset.univ a (fun d => m d*f d) hb hε
      (fun d _ => ha d) (fun d _ => (hmf d).trans (by linarith)) (fun d _ => he d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

theorem allocatedUnitProfileWidth_inverse_exp (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ)+1 ≤ Real.exp P) :
    (allocatedUnitProfileWidth R σ a)⁻¹ ≤ Real.exp (4*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hLX : ((1 : ℕ) : ℝ) ≤ X := by norm_num; linarith
  have h := allocatedWidthFloor_inverse_power_bound 1 0 0 a le_rfl hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) (haP.trans hPX) hLX
  simpa only [allocatedUnitProfileWidth, X, ← Real.exp_nat_mul, Nat.zero_add, Nat.cast_ofNat] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedLongJet_scaled_density
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hσ1 : ∀ j, σ j ≤ 1) (z : AllocatedLongJetRows B U basis S O) :
    (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
      allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z =
    ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a *
      allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a) := by
  simp only [allocatedLongJetDensity, Finset.prod_mul_distrib]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_le_exp (q h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInterpolationAllowance q h κ ≤
      Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2)) := by
  have hq : (q : ℝ) ≤ Real.exp q := by linarith [Real.add_one_le_exp (q : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hterm : (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp q * (Real.exp 1 * (Real.exp ((q : ℝ)^2) * Real.exp b)) := by
        gcongr
        exact factorial_le_exp_sq q
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have he : 1 ≤ Real.exp ((q : ℝ)^2 + q + b + 1) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hbase : 1 + (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 2) := by
    calc
      _ ≤ 2 * Real.exp ((q : ℝ)^2 + q + b + 1) := by linarith
      _ ≤ Real.exp 1 * Real.exp ((q : ℝ)^2 + q + b + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  unfold kernelJetInterpolationAllowance
  calc
    _ ≤ (Real.exp ((q : ℝ)^2 + q + b + 2)) ^ h := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem kernelJetEntryAllowance_le_exp (q h : ℕ) :
    kernelJetEntryAllowance q h ≤ Real.exp ((q : ℝ) * (h + 1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq := Real.add_one_le_exp (q : ℝ)
  unfold kernelJetEntryAllowance
  calc
    _ ≤ (Real.exp 1) ^ q * (Real.exp q) ^ h := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem kernelJetMinorThreshold_inv_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    (kernelJetMinorThreshold q n j h κ)⁻¹ ≤
      Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hQ := kernelJetInterpolationAllowance_le_exp q h hκ hb hi
  have hQpos := (kernelJetInterpolationAllowance_pos q h hκ).le
  simp only [kernelJetMinorThreshold, one_div, inv_inv]
  calc
    _ ≤ ((Real.exp n) ^ h *
        Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2))) ^ j := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]

theorem kernelJetInverseAllowance_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInverseAllowance q n j h κ ≤
      Real.exp ((j : ℝ) + (j : ℝ)^2 +
        (j - 1 : ℕ) * ((q : ℝ) * (h + 1)) +
        j * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hE := kernelJetEntryAllowance_le_exp q h
  have hEin := (kernelJetEntryAllowance_pos q h).le
  have hminor := kernelJetMinorThreshold_inv_le_exp q n j h hκ hb hi
  have hminorpos := (kernelJetMinorThreshold_pos q n j h hκ).le
  unfold kernelJetInverseAllowance
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp j * ((Real.exp ((j : ℝ)^2) *
        (Real.exp ((q : ℝ) * (h + 1))) ^ (j - 1)) *
        Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2)))) := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem scalarKernel_real_entry_bound {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L : ℕ} (hL : 0 < L)
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ) (rows : O → Finset α)
    (i : O) (a : BoundedIntegerExponent J degree) :
    |normalizedScalarKernelJet x degree rows i a| ≤ kernelJetEntryAllowance (Fintype.card α) degree := by
  have hc (j : J) (i : Option α) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  exact boundedDegreeRealJetMatrix_entry_bound _ _ (fun j => hc j none)
    (fun i j => hc j (some i)) degree rows i a

theorem scalarKernelFixed_operator_bounds {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ} (hL : 0 < L)
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) :
    ‖(scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap‖ ≤
      Fintype.card O * kernelJetEntryAllowance (Fintype.card α) degree ∧
    ‖scalarKernelFixedFree x degree rows s‖ ≤
      Fintype.card (UnselectedColumn s) * kernelJetEntryAllowance (Fintype.card α) degree := by
  constructor
  · rw [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
      normalized_scalarKernel_pivot x degree rows s one_ne_zero]
    exact matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos _ _).le
      (fun i j => scalarKernel_real_entry_bound hL x degree rows i (s j))
  · exact matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos _ _).le
      (fun i j => scalarKernel_real_entry_bound hL x degree rows i j.val)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem kernelGeometryLog_bounds (q n j k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelGeometryLog q n j k d p ∧ p ≤ kernelGeometryLog q n j k d p ∧
    kernelInverseLog q n j d p ≤ kernelGeometryLog q n j k d p ∧
    (j : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p ∧
    (k : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p := by
  have hi : 0 ≤ kernelInverseLog q n j d p := by unfold kernelInverseLog; positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he : 0 ≤ (q : ℝ) * (d + 1) := by positivity
  unfold kernelGeometryLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nat_mul_kernelEntry_le_exp (a q d : ℕ) :
    (a : ℝ) * kernelJetEntryAllowance q d ≤ Real.exp ((a : ℝ) + (q : ℝ) * (d + 1)) := by
  have ha : (a : ℝ) ≤ Real.exp a := by linarith [Real.add_one_le_exp (a : ℝ)]
  calc
    _ ≤ Real.exp a * Real.exp ((q : ℝ) * (d + 1)) :=
      mul_le_mul ha (kernelJetEntryAllowance_le_exp q d) (kernelJetEntryAllowance_pos q d).le (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem fixedKernel_geometry_le_exp {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (x : J → IntegerScalarCubeBox α L) (d : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J d)
    (hs : ((scalarKernelIntegerJet x d rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card O) d (1/(M : ℝ)))
    {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p) :
    let P := kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent J d)) d p
    ‖(scalarKernelFixedPivot hL x d rows s hs).toContinuousLinearMap‖ ≤ Real.exp P ∧
    ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤ Real.exp P ∧
    ‖scalarKernelFixedFree x d rows s‖ ≤ Real.exp P := by
  dsimp only
  have hb := kernelGeometryLog_bounds (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d hp
  have he := scalarKernelFixed_operator_bounds hL x d rows s hs
  have hcard : Fintype.card (UnselectedColumn s) ≤ Fintype.card (BoundedIntegerExponent J d) :=
    Fintype.card_subtype_le _
  refine ⟨he.1.trans ((nat_mul_kernelEntry_le_exp _ _ _).trans (Real.exp_le_exp.mpr hb.2.2.2.1)), ?_, ?_⟩
  · apply hi.trans
    apply (kernelJetInverseAllowance_le_exp (Fintype.card α) (Fintype.card J) (Fintype.card O) d
      (one_div_pos.mpr (by exact_mod_cast hM)) hp (by simpa only [one_div, inv_inv] using hMp)).trans
    exact Real.exp_le_exp.mpr hb.2.2.1
  · apply he.2.trans
    apply (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤
      Fintype.card (BoundedIntegerExponent J d)) (kernelJetEntryAllowance_pos _ _).le).trans
    exact (nat_mul_kernelEntry_le_exp _ _ _).trans (Real.exp_le_exp.mpr hb.2.2.2.2)

theorem kernelRowOutputLog_nonneg (q n j k u d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelRowOutputLog q n j k u d p := by
  have hP := (kernelGeometryLog_bounds q n j k d hp).1
  have hf := affineProfileLogBound_nonneg k hp
  have hr := jetOutputRadiusLog_nonneg q u d hP
  unfold kernelRowOutputLog
  positivity

theorem fixedKernel_output_le_exp {α J O N : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (x : J → IntegerScalarCubeBox α L) (d : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J d)
    (hs : ((scalarKernelIntegerJet x d rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card O) d (1/(M : ℝ)))
    (δ R : ℝ≥0) (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : (R : ℝ) ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let E := scalarKernelFixedPivot hL x d rows s hs
    let F := scalarKernelFixedFree x d rows s
    let B := kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent J d)) (Fintype.card N) d p
    (pivotKernelCap (UnselectedColumn s) E R (δ⁻¹^Fintype.card (BoundedIntegerExponent J d)) : ℝ) ≤ Real.exp B ∧
    (pivotKernelLip (UnselectedColumn s) E R (affineProductProfileLip (BoundedIntegerExponent J d) δ) : ℝ) ≤ Real.exp B ∧
    (normalizedJetOutputRadius α N E F d R R : ℝ) ≤ Real.exp B := by
  dsimp only
  let P := kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d p
  have hb := kernelGeometryLog_bounds (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d hp
  have hnorm := fixedKernel_geometry_le_exp hL hM x d rows s hs hi hp hMp
  have hP : 0 ≤ P := hb.1
  have hRP : (R : ℝ) ≤ Real.exp P := hR.trans (Real.exp_le_exp.mpr hb.2.1)
  have hprof := affineProfileLogBound_nonneg (Fintype.card (BoundedIntegerExponent J d)) hp
  have hrad := jetOutputRadiusLog_nonneg (Fintype.card α) (Fintype.card N) d hb.1
  have hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤ Fintype.card (BoundedIntegerExponent J d) :=
    by exact_mod_cast Fintype.card_subtype_le (fun a : BoundedIntegerExponent J d => a ∉ Set.range s)
  have hmul := mul_le_mul_of_nonneg_right hcard (by linarith : 0 ≤ P + 1)
  have hcap : ((δ⁻¹^Fintype.card (BoundedIntegerExponent J d) : ℝ≥0) : ℝ) ≤
      Real.exp (affineProfileLogBound (Fintype.card (BoundedIntegerExponent J d)) p) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap_le_exp _ (show (0 : ℝ) < δ from hδ) hp hδp
  refine ⟨?_, ?_, ?_⟩
  · apply (pivotKernelCap_le_exp _ _ R _ hnorm.2.1 hRP hcap).trans
    apply Real.exp_le_exp.mpr
    dsimp [kernelRowOutputLog]
    nlinarith [hb.1]
  · apply (pivotKernelLip_le_exp _ _ R _ hnorm.2.1 hRP
      (affineProductProfileLip_le_exp (BoundedIntegerExponent J d) hδp)).trans
    apply Real.exp_le_exp.mpr
    dsimp [kernelRowOutputLog]
    linarith
  · apply (normalizedJetOutputRadius_le_exp α N _ _ d R R hb.1 hnorm.1 hnorm.2.2 hRP hRP).trans
    apply Real.exp_le_exp.mpr
    have hbase : 0 ≤ (Fintype.card O : ℝ)^2 + (Fintype.card O + 1) * P +
        affineProfileLogBound (Fintype.card (BoundedIntegerExponent J d)) p +
        Fintype.card (BoundedIntegerExponent J d) * (P + 1) := by positivity
    dsimp [kernelRowOutputLog]
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelComparisonScales
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem kernelFamilyOutputLog_nonneg {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) : 0 ≤ kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact add_nonneg zero_le_one (Finset.sum_nonneg (fun q _ => kernelRowOutputLog_nonneg _ _ _ _ _ _ hp))

theorem kernelRowOutputLog_le_family {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (q : Q) :
    kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p ≤
        kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact (Finset.single_le_sum (fun r _ => kernelRowOutputLog_nonneg (Fintype.card α) (Fintype.card J)
      (Fintype.card (O r)) (Fintype.card (BoundedIntegerExponent J (degree r))) (Fintype.card (N r)) (degree r) hp)
    (Finset.mem_univ q)).trans (le_add_of_nonneg_left zero_le_one)

theorem fixedKernel_family_output_bound {Q α J : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O N : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)] [∀ q, Fintype (N q)]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) (x : J → IntegerScalarCubeBox α L)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q))
    (hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0)
    (hi : ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) (1/(M : ℝ)))
    (δ R : Q → ℝ≥0) (hδ : ∀ q, 0 < δ q) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : ∀ q, (R q : ℝ) ≤ Real.exp p) (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p)
    (H : Q → ℝ) (hH : ∀ q, 0 < H q) :
    let C : ℝ≥0 := ⟨Real.exp (kernelFamilyOutputLog (α := α) (J := J) O N degree p), (Real.exp_pos _).le⟩
    let E := fun q => normalizedPivotEquiv _ (hs q)
      (fun i => kernelJetCoefficientScale J (degree q) L (H q) (s q i)) (fun _ => H q)
      (fun i => kernelJetCoefficientScale_pos J (degree q) (by exact_mod_cast hL) (hH q) (s q i))
      (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns
      (remainingMatrixColumns (scalarKernelIntegerJet x (degree q) (rows q)) (s q))
      (fun j => kernelJetCoefficientScale J (degree q) L (H q) j.val) (fun _ => H q))
    1 ≤ C ∧
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q)
      ((δ q)⁻¹^Fintype.card (BoundedIntegerExponent J (degree q))) ≤ C) ∧
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q)
      (affineProductProfileLip (BoundedIntegerExponent J (degree q)) (δ q)) ≤ C) ∧
    (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ C) := by
  dsimp only
  have hE (q) := scalarKernel_pivot_scale_independent hL x (degree q) (rows q) (s q) (hs q) (hH q)
  have hF (q) := scalarKernel_free_scale_independent x (degree q) (rows q) (s q) (hH q).ne'
  simp_rw [hE, hF]
  have hrow (q) := fixedKernel_output_le_exp (N := N q) hL hM x (degree q) (rows q) (s q) (hs q)
    (hi q) (δ q) (R q) (hδ q) hp hMp (hR q) (hδp q)
  have hbound (q) := Real.exp_le_exp.mpr (kernelRowOutputLog_le_family (α := α) (J := J) O N degree hp q)
  refine ⟨?_, fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact_mod_cast Real.one_le_exp_iff.mpr (kernelFamilyOutputLog_nonneg (α := α) (J := J) O N degree hp)
  · exact_mod_cast (hrow q).1.trans (hbound q)
  · exact_mod_cast (hrow q).2.1.trans (hbound q)
  · exact_mod_cast (hrow q).2.2.trans (hbound q)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem principalAxisParameter_card_le {D α : Type*} [Fintype D] [Fintype α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] :
    Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P) ≤
      Fintype.card (JointBlockParameter B h α) := by
  apply Fintype.card_le_of_injective
    (fun z : PrincipalAxisParameter (B := B) (h := h) (α := α) P =>
      (⟨z.1.val, z.2⟩ : JointBlockParameter B h α))
  intro a b hab
  rcases a with ⟨⟨a, ha⟩, x⟩
  rcases b with ⟨⟨b, hb⟩, y⟩
  cases hab
  rfl

theorem principalAxisColumnLip_le_exp {D α : Type*} [Fintype D] [Fintype α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] (n d : ℕ) :
    (n : ℝ) * polynomialBoxLip
        (Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P))
        d (normalizedJetMass α d) ≤
      Real.exp (n + 3*(Fintype.card (JointBlockParameter B h α) : ℝ)*d +
        (Fintype.card α : ℝ)*(d+1)) := by
  apply (normalizedJetColumnLip_le_exp α n _ d).trans
  apply Real.exp_le_exp.mpr
  have hc := principalAxisParameter_card_le (α := α) B h P
  gcongr

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedDensityLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    let K := kernelFamilyOutputLog (α := α) (J := G) O
      (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8))
    0 ≤ allocatedDensityLog (G := G) B α O P ∧
      K ≤ allocatedDensityLog (G := G) B α O P ∧
      ∀ j, K + allocatedDensityColumnLog (G := G) B α j + P ≤
        allocatedDensityLog (G := G) B α O P := by
  dsimp only
  have hK := kernelFamilyOutputLog_nonneg (α := α) (J := G) O
    (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1)
    (show 0 ≤ 4*(P+8) by positivity)
  have hj (j : Fin m) : 0 ≤ allocatedDensityColumnLog (G := G) B α j := by
    unfold allocatedDensityColumnLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedDensityLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have h := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "budget" => allocatedDensityLog (G := G) B α O P
local notation "bound" => NNReal.mk (Real.exp budget) (le_of_lt (Real.exp_pos budget))
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" j => NNReal.mk
  (allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (Fin.val j+1))))
  (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedDensityKernel_bounds (j : Fin m) {H : ℝ} (hH : 0 < H) :
    let E := normalizedPivotEquiv _ (hA j)
      (fun o => kernelJetCoefficientScale G (j.val+1) S.value H (s j o)) (fun _ => H)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) hH (s j o))
      (fun _ => hH)
    pivotKernelCap (UnselectedColumn (s j)) E (radius j)
        ((delta j)⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1))) ≤ bound ∧
      pivotKernelLip (UnselectedColumn (s j)) E (radius j)
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) (delta j)) *
        (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
          polynomialBoxLip
            (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
              (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) *
        (radius j) ≤ bound := by
  dsimp only
  have hp' : 0 ≤ 4*(P+8) := by positivity
  have hPP : Real.exp P ≤ Real.exp (4*(P+8)) := Real.exp_le_exp.mpr (by linarith)
  have hb := allocatedDensityLog_bounds (G := G) B α O hP
  have hf := fixedKernel_family_output_bound (N := AllocatedNonkernelCoefficient (G := G) B)
    S.positive hM x (fun j : Fin m => j.val+1) rows s hA hi
    (fun j => delta j) (fun j => radius j)
    (fun j => allocatedUnitProfileWidth_pos (hR j) (hσ j) _) hp' (hMP.trans hPP)
    (fun j => (hRP j).trans hPP)
    (fun j => allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (fun _ => H) (fun _ => hH)
  let K := kernelFamilyOutputLog (α := α) (J := G) O
    (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8))
  constructor
  · exact (hf.2.1 j).trans (by exact_mod_cast Real.exp_le_exp.mpr hb.2.1)
  · apply NNReal.coe_le_coe.mp
    have hmid :
        (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) : ℝ) *
          polynomialBoxLip
            (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
              (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1)) ≤
        Real.exp (allocatedDensityColumnLog (G := G) B α j) := by
      convert principalAxisColumnLip_le_exp (α := α) B (layerSamplerDegree I n)
        (fun a => ¬grid a) (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j)) (j.val+1) using 1
      congr 1
      simp only [allocatedDensityColumnLog, Nat.cast_add, Nat.cast_one]
      ring
    have hlip := hf.2.2.1 j
    have hlip' := NNReal.coe_le_coe.mpr hlip
    simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_mk]
    calc
      _ ≤ Real.exp K * Real.exp (allocatedDensityColumnLog (G := G) B α j) * Real.exp P :=
        mul_le_mul (mul_le_mul hlip' hmid (by positivity) (Real.exp_pos _).le)
          (hRP j) (hR j).le (by positivity)
      _ = Real.exp (K + allocatedDensityColumnLog (G := G) B α j + P) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp budget := Real.exp_le_exp.mpr (hb.2.2 j)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedContinuousKernelDensity_exp_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j) (z : O j → ℝ) :
    (∀ y, |allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzOnWith bound
        (fun y => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z)
        (Metric.closedBall 0 1) := by
  have hb := allocatedDensityKernel_bounds B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j zero_lt_one
  have hd := allocatedContinuousKernelDensity_bounds_s2 B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) z
  exact ⟨fun y => (hd.1 y).trans (by exact_mod_cast hb.1), hd.2.weaken hb.2⟩

theorem allocatedIntegerKernelDensity_exp_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j)) (z : O j → ℝ) :
    (∀ y, |allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzOnWith bound
        (fun y => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z)
        (Metric.closedBall 0 1) := by
  have hb := allocatedDensityKernel_bounds B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
  have hd := allocatedIntegerKernelDensity_bounds_s2 B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) z
  exact ⟨fun y => (hd.1 y).trans (by exact_mod_cast hb.1), hd.2.weaken hb.2⟩

theorem allocatedLongJetTarget_exp_bounds (hσ1 : ∀ j, σ j ≤ 1) :
    1 ≤ bound ∧
      (∀ y a z, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ bound) ∧
      (∀ a z, LipschitzOnWith bound
        (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z) (Metric.closedBall 0 1)) := by
  have hrow (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val) :
      (∀ y, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ bound) ∧
        LipschitzOnWith bound (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z)
          (Metric.closedBall 0 1) := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i =>
      exact allocatedContinuousKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i z
    | inr i =>
      exact allocatedIntegerKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i
        (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))
  refine ⟨?_, fun y a z => (hrow a z).1 y, fun a z => (hrow a z).2⟩
  exact_mod_cast Real.one_le_exp_iff.mpr (allocatedDensityLog_bounds (G := G) B α O hP).1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)

theorem allocatedLongJetTarget_normalized (y : activeInput → ℝ)
    (z : AllocatedLongJetRows B U basis S O) (a : {a // ¬grid a}) :
    allocatedLongJetTarget B U basis S x u rows s hA y a (z a) =
      allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a
        (fun o => allocatedLongJetRealCoordinates B U basis S z ⟨a, o⟩) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteCoefficientL1
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedLongJet_residue_coefficient_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, p.weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j)
    (z : AllocatedLongJetRows B U basis S O) :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let normalized := fun v => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v
    |p.mean (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
        allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (normalized v) (allocatedLongJetRealCoordinates B U basis S z))| ≤
      Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a} := by
  intro C CM normalized
  have hreplace := allocatedFixedKernel_replacement_s2 B U basis hR hσ S x rows hM selection hx hq
    hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge modulus hperiod s hA hi u p residue hr
  have hcap := (allocatedLongJetTarget_exp_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1).2.1
  have hCM : 1 ≤ CM := by
    change (1 : ℝ) ≤ (layerKernelIndexBound m M : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  have hm (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
        allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ CM := by
    rcases a with ⟨⟨j,a⟩, ha⟩
    cases a with
    | inl i => exact ⟨zero_le_one, hCM⟩
    | inr i => exact (hreplace j i (Nat.lt_of_not_ge ha)).1 _
  have herr (v) (hv : p.weight v ≠ 0) (a : {a // ¬grid a}) :
      |allocatedLongJetOutputScale B U basis S (O := O) a *
          allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a) -
        allocatedLongJetMask B U basis S x rows modulus residue a (z a) *
          allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a)| ≤ ε := by
    rcases a with ⟨⟨j,a⟩, ha⟩
    cases a with
    | inl i => simpa only [allocatedLongJetOutputScale, allocatedLongJetFactor,
        allocatedLongJetMask, allocatedLongJetTarget, normalized, sub_self, abs_zero] using hε.le
    | inr i => exact (hreplace j i (Nat.lt_of_not_ge ha)).2 v hv _
  have hid (v) : allocatedNormalizedLongJetDensity B U basis S x u rows s hA
      (normalized v) (allocatedLongJetRealCoordinates B U basis S z) =
      ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a) := by
    exact Finset.prod_congr rfl (fun a _ =>
      (allocatedLongJetTarget_normalized B U basis S x u rows s hA (normalized v) z a).symm)
  simp_rw [hid]
  rw [← p.mean_const_mul, ← p.mean_sub]
  apply p.abs_mean_le_on_support
  intro v hv
  rw [allocatedLongJet_scaled_density]
  exact masked_product_error _ _ _ (Real.exp_nonneg _) (zero_le_one.trans hCM) hε.le
    (fun a => hcap _ a (z a))
    (fun a => by rw [abs_of_nonneg (hm a).1]; exact (hm a).2) (herr v hv)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueCoefficientL1
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedLongJet_residue_coefficient_l1_s2_oai {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, p.weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j)
 :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let normalized := fun v => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v
    let proxy := fun z => p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA (normalized v) z)
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue proxy)
      (allocatedLongJetReference B U basis S O) ∧
    (∫ z, |p.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) := by
  intro C CM T normalized proxy
  have hid (v) (z : AllocatedLongJetRows B U basis S O) :
      allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (normalized v) (allocatedLongJetRealCoordinates B U basis S z) =
      ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a) := by
    exact Finset.prod_congr rfl (fun a _ =>
      (allocatedLongJetTarget_normalized B U basis S x u rows s hA (normalized v) z a).symm)
  have he (z) := allocatedLongJet_residue_coefficient_comparison B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u p residue hr z
  change ∀ z, |_ - _ * p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
    (normalized v) (allocatedLongJetRealCoordinates B U basis S z))| ≤
      Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a} at he
  simp_rw [hid] at he
  have hε0 : 0 ≤ Fintype.card {a // ¬grid a} * ε *
      (1 + CM * C + ε)^Fintype.card {a // ¬grid a} := by
    dsimp [CM,C]
    positivity
  have hh := allocatedFiniteLongJet_l1_comparison_s2 B U basis hR hσ S x u rows s hA
    hM hi hP hMP hRP hRi hσi hcount hσ1 p modulus residue hε0 he
  have hprofile : allocatedLongProfileDensity B U basis S x rows modulus residue proxy =
      fun z => (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        p.mean (fun v => ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a)) /
        (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) := by
    funext z
    dsimp only [allocatedLongProfileDensity, proxy]
    simp_rw [hid]
  rw [hprofile]
  exact hh

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_l1_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_l1_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
