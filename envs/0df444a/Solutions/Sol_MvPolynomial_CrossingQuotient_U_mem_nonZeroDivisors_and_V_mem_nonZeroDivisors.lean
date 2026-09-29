-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/224c70ea-dadd-53e0-8ddb-a05beab6c7de

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

open scoped Polynomial LaurentPolynomial

namespace NZDKIT

universe u

variable {W : Type u} [CommRing W] (t : W)

noncomputable def gen₁ : Fin 2 → W[T;T⁻¹] :=
  ![LaurentPolynomial.T 1, LaurentPolynomial.C t * LaurentPolynomial.T (-1)]

noncomputable def gen₂ : Fin 2 → W[T;T⁻¹] :=
  ![LaurentPolynomial.C t * LaurentPolynomial.T 1, LaurentPolynomial.T (-1)]

theorem gen₁_zero : gen₁ t 0 = LaurentPolynomial.T 1 := rfl
theorem gen₁_one : gen₁ t 1 = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := rfl
theorem gen₂_zero : gen₂ t 0 = LaurentPolynomial.C t * LaurentPolynomial.T 1 := rfl
theorem gen₂_one : gen₂ t 1 = LaurentPolynomial.T (-1) := rfl

theorem T_one_mul_T_neg_one :
    (LaurentPolynomial.T 1 : W[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; rfl

theorem rel₁ : (LaurentPolynomial.T 1 : W[T;T⁻¹]) * (LaurentPolynomial.C t * LaurentPolynomial.T (-1))
    = LaurentPolynomial.C t := by
  rw [mul_left_comm, T_one_mul_T_neg_one, mul_one]

theorem rel₂ : (LaurentPolynomial.C t * LaurentPolynomial.T 1 : W[T;T⁻¹]) * LaurentPolynomial.T (-1)
    = LaurentPolynomial.C t := by
  rw [mul_assoc, T_one_mul_T_neg_one, mul_one]

theorem aeval_gen₁_rel : aeval (gen₁ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₁_zero, gen₁_one, rel₁,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

theorem aeval_gen₂_rel : aeval (gen₂ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₂_zero, gen₂_one, rel₂,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

noncomputable def φ₁ : CrossingQuotient W t →ₐ[W] W[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (gen₁ t)) (fun p hp => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, aeval_gen₁_rel, mul_zero])

noncomputable def φ₂ : CrossingQuotient W t →ₐ[W] W[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (gen₂ t)) (fun p hp => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, aeval_gen₂_rel, mul_zero])

theorem φ₁_mk (p : MvPolynomial (Fin 2) W) : φ₁ t (mk t p) = aeval (gen₁ t) p := rfl
theorem φ₂_mk (p : MvPolynomial (Fin 2) W) : φ₂ t (mk t p) = aeval (gen₂ t) p := rfl

theorem φ₁_monomial (n : ℤ) :
    φ₁ t (monomial t n) = LaurentPolynomial.C (t ^ (-n).toNat) * LaurentPolynomial.T n := by
  rcases le_or_gt 0 n with h | h
  · rw [monomial_of_nonneg t h, map_pow, φ₁_mk, aeval_X, gen₁_zero, LaurentPolynomial.T_pow,
      mul_one, Int.toNat_of_nonneg h, Int.toNat_of_nonpos (neg_nonpos.mpr h), pow_zero, map_one,
      one_mul]
  · rw [monomial_of_neg t h, map_pow, φ₁_mk, aeval_X, gen₁_one, mul_pow, ← map_pow,
      LaurentPolynomial.T_pow, mul_neg_one, Int.toNat_of_nonneg (by omega : 0 ≤ -n), neg_neg]

theorem φ₁_repr (c : ℤ →₀ W) :
    φ₁ t (c.sum fun n r => r • monomial t n)
      = c.sum fun n r => AddMonoidAlgebra.single n (r * t ^ (-n).toNat) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [map_smul, φ₁_monomial, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    LaurentPolynomial.single_eq_C_mul_T]

theorem coeff_φ₁_repr (c : ℤ →₀ W) (m : ℤ) :
    (φ₁ t (c.sum fun n r => r • monomial t n)).coeff m = c m * t ^ (-m).toNat := by
  rw [φ₁_repr, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_single]
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m]
  · rw [Finsupp.single_eq_same]
  · intro n _ hn
    rw [Finsupp.single_apply, if_neg hn]
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm, zero_mul, Finsupp.single_zero, Finsupp.zero_apply]

theorem exists_repr (a : CrossingQuotient W t) :
    ∃ c : ℤ →₀ W, (c.sum fun n r => r • monomial t n) = a := by
  have h := (MvPolynomial.CrossingQuotient.linearIndependent_monomial_and_span_eq_top t).2
  have ha : a ∈ Submodule.span W (Set.range (monomial t)) := by rw [h]; trivial
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp ha

theorem φ₁_injective_of_mem (ht : t ∈ nonZeroDivisors W) : Function.Injective (φ₁ t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨c, rfl⟩ := exists_repr t a
  suffices hc : c = 0 by rw [hc, Finsupp.sum_zero_index]
  ext m
  have hm := coeff_φ₁_repr t c m
  rw [ha] at hm
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hm
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ht _)).mp hm.symm

theorem mem_nonZeroDivisors_of_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (ha : f a ∈ nonZeroDivisors B) : a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  apply hf
  rw [map_zero]
  exact (mem_nonZeroDivisors_iff_right.mp ha) (f b) (by rw [← map_mul, hb, map_zero])

theorem mem_nonZeroDivisors_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {a : A} (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  have : e.symm b * a = 0 := by
    apply e.injective
    rw [map_mul, e.apply_symm_apply, map_zero, hb]
  have h2 := (mem_nonZeroDivisors_iff_right.mp ha) _ this
  simpa using congrArg e h2

theorem T_one_sub_C_mem (a : W) :
    (LaurentPolynomial.T 1 - LaurentPolynomial.C a : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  nontriviality W
  have hmon : (Polynomial.X - Polynomial.C a : W[X]).Monic := Polynomial.monic_X_sub_C a
  have h1 : (Polynomial.X - Polynomial.C a : W[X]) ∈ nonZeroDivisors W[X] := hmon.mem_nonZeroDivisors
  have h2 := IsLocalization.nonZeroDivisors_le_comap (M := .powers (Polynomial.X : W[X]))
    (S := W[T;T⁻¹]) h1
  rw [Submonoid.mem_comap, LaurentPolynomial.algebraMap_eq_toLaurent, map_sub, Polynomial.toLaurent_X,
    Polynomial.toLaurent_C] at h2
  exact h2

theorem one_sub_C_mul_T_neg_one_mem (a : W) :
    (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1) : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  have h : (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1) : W[T;T⁻¹])
      = LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 - LaurentPolynomial.C a) := by
    rw [mul_sub, ← LaurentPolynomial.T_add, mul_comm]
    rfl
  rw [h]
  exact mul_mem (LaurentPolynomial.isUnit_T (-1)).mem_nonZeroDivisors (T_one_sub_C_mem a)

theorem one_sub_C_mul_T_one_mem (a : W) :
    (1 - LaurentPolynomial.C a * LaurentPolynomial.T 1 : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  have h := mem_nonZeroDivisors_of_ringEquiv (LaurentPolynomial.invert (R := W)).toRingEquiv
    (one_sub_C_mul_T_neg_one_mem a)
  have h2 : (LaurentPolynomial.invert (R := W)).toRingEquiv
      (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1)) = 1 - LaurentPolynomial.C a * LaurentPolynomial.T 1 := by
    change LaurentPolynomial.invert (1 - LaurentPolynomial.C a * LaurentPolynomial.T (-1)) = _
    rw [map_sub, map_one, map_mul, LaurentPolynomial.invert_T, neg_neg, LaurentPolynomial.invert_C]
  rwa [h2] at h

theorem C_mul_T_mem (ht : t ∈ nonZeroDivisors W) (n : ℤ) :
    (LaurentPolynomial.C t * LaurentPolynomial.T n : W[T;T⁻¹]) ∈ nonZeroDivisors W[T;T⁻¹] := by
  refine mul_mem ?_ (LaurentPolynomial.isUnit_T n).mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro f hf

  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro m
  have := AddMonoidAlgebra.coeff_mul_single_zero f t m
  rw [LaurentPolynomial.single_eq_C] at this
  change (f * LaurentPolynomial.C t : W[T;T⁻¹]).coeff m = f.coeff m * t at this
  rw [hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  exact ((mul_right_mem_nonZeroDivisors_eq_zero_iff ht).mp this.symm)

theorem φ₁_U : φ₁ t (U t) = LaurentPolynomial.T 1 := by
  rw [show U t = mk t (X 0) from rfl, φ₁_mk, aeval_X, gen₁_zero]

theorem φ₁_V : φ₁ t (V t) = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := by
  rw [show V t = mk t (X 1) from rfl, φ₁_mk, aeval_X, gen₁_one]

theorem N1 (ht : t ∈ nonZeroDivisors W) :
    U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧ V t ∈ nonZeroDivisors (CrossingQuotient W t) := by
  refine ⟨mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_,
    mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_⟩
  · change φ₁ t (U t) ∈ _
    rw [φ₁_U]
    exact (LaurentPolynomial.isUnit_T 1).mem_nonZeroDivisors
  · change φ₁ t (V t) ∈ _
    rw [φ₁_V]
    exact C_mul_T_mem t ht (-1)

theorem N2 (ht : t ∈ nonZeroDivisors W) (w : W) :
    1 - algebraMap W (CrossingQuotient W t) w * U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧
      1 - algebraMap W (CrossingQuotient W t) w * V t ∈ nonZeroDivisors (CrossingQuotient W t) := by
  refine ⟨mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_,
    mem_nonZeroDivisors_of_injective (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])
      (φ₁_injective_of_mem t ht) ?_⟩
  · change φ₁ t (1 - algebraMap W (CrossingQuotient W t) w * U t) ∈ _
    rw [map_sub, map_one, map_mul, AlgHom.commutes, φ₁_U, ← LaurentPolynomial.C_eq_algebraMap]
    exact one_sub_C_mul_T_one_mem w
  · change φ₁ t (1 - algebraMap W (CrossingQuotient W t) w * V t) ∈ _
    rw [map_sub, map_one, map_mul, AlgHom.commutes, φ₁_V, ← LaurentPolynomial.C_eq_algebraMap,
      ← mul_assoc, ← map_mul]
    exact one_sub_C_mul_T_neg_one_mem (w * t)

end NZDKIT

theorem solution
    {W : Type*} [CommRing W] (t : W) (ht : t ∈ nonZeroDivisors W) :
    U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧ V t ∈ nonZeroDivisors (CrossingQuotient W t) :=
  NZDKIT.N1 t ht

end S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors (solution)
