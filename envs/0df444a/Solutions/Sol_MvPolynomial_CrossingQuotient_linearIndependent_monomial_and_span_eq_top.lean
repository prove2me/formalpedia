-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.linearIndependent_monomial_and_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e89bfd12-2e4a-5d34-a460-36039ee4fb6a

import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient Module

noncomputable section

namespace L9Core

variable {W : Type*} [CommRing W] (t : W)

def coordAux : MvPolynomial (Fin 2) W →ₗ[W] (ℤ →₀ W) :=
  (MvPolynomial.basisMonomials (Fin 2) W).constr W
    fun d => t ^ min (d 0) (d 1) • Finsupp.single ((d 0 : ℤ) - d 1) (1 : W)

theorem coordAux_monomial (d : Fin 2 →₀ ℕ) (c : W) :
    coordAux t (MvPolynomial.monomial d c)
      = c • (t ^ min (d 0) (d 1) • Finsupp.single ((d 0 : ℤ) - d 1) (1 : W)) := by
  have h : MvPolynomial.monomial d c = c • MvPolynomial.basisMonomials (Fin 2) W d := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, coordAux, Module.Basis.constr_basis]

theorem coordAux_mul_gen (p : MvPolynomial (Fin 2) W) : coordAux t (p * (X 0 * X 1 - C t)) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    set s : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hs
    have hXY : (X 0 * X 1 : MvPolynomial (Fin 2) W) = MvPolynomial.monomial s 1 := by
      rw [hs, X, X, MvPolynomial.monomial_mul, mul_one]
    have e1 : MvPolynomial.monomial d c * (X 0 * X 1 - C t : MvPolynomial (Fin 2) W)
        = MvPolynomial.monomial (d + s) c - MvPolynomial.monomial d (c * t) := by
      rw [mul_sub, hXY, MvPolynomial.monomial_mul, mul_one, C_apply, MvPolynomial.monomial_mul, add_zero]
    rw [e1, map_sub, coordAux_monomial, coordAux_monomial]
    have h0 : (d + s) 0 = d 0 + 1 := by
      rw [hs, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
        if_neg (show (1 : Fin 2) ≠ 0 by decide), add_zero]
    have h1 : (d + s) 1 = d 1 + 1 := by
      rw [hs, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (show (0 : Fin 2) ≠ 1 by decide), if_pos rfl, zero_add]
    rw [h0, h1, min_add_add_right]
    have h2 : ((d 0 + 1 : ℕ) : ℤ) - ((d 1 + 1 : ℕ) : ℤ) = (d 0 : ℤ) - d 1 := by push_cast; ring
    rw [h2, smul_smul, smul_smul, ← sub_smul]
    have h3 : c * t ^ (min (d 0) (d 1) + 1) - c * t * t ^ min (d 0) (d 1) = 0 := by ring
    rw [h3, zero_smul]
  | add p q hp hq => rw [add_mul, map_add, hp, hq, add_zero]

theorem coordAux_eq_zero_of_mem {p : MvPolynomial (Fin 2) W}
    (hp : p ∈ Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) : coordAux t p = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  exact coordAux_mul_gen t a

def rep (n : ℤ) : MvPolynomial (Fin 2) W := if 0 ≤ n then X 0 ^ n.toNat else X 1 ^ (-n).toNat

theorem mk_rep (n : ℤ) : mk t (rep n) = MvPolynomial.CrossingQuotient.monomial t n := by
  unfold rep MvPolynomial.CrossingQuotient.monomial
  split_ifs <;> rw [map_pow]

theorem coordAux_rep (n : ℤ) : coordAux t (rep n) = Finsupp.single n 1 := by
  unfold rep
  split_ifs with h
  · rw [X_pow_eq_monomial, coordAux_monomial, one_smul, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
      if_neg (show (0 : Fin 2) ≠ 1 by decide), Nat.min_zero, pow_zero, one_smul, Nat.cast_zero, sub_zero,
      Int.toNat_of_nonneg h]
  · rw [X_pow_eq_monomial, coordAux_monomial, one_smul, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (show (1 : Fin 2) ≠ 0 by decide), if_pos rfl, Nat.zero_min, pow_zero, one_smul, Nat.cast_zero, zero_sub,
      Int.toNat_of_nonneg (by omega), neg_neg]

theorem linearIndependent_monomial : LinearIndependent W (MvPolynomial.CrossingQuotient.monomial t) := by
  rw [linearIndependent_iff']
  intro s g hg i hi

  have h1 : mk t (∑ n ∈ s, g n • rep n) = 0 := by
    rw [map_sum]
    simp only [map_smul, mk_rep]
    exact hg
  rw [mk_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 := coordAux_eq_zero_of_mem t h1
  rw [map_sum] at h2
  simp only [map_smul, coordAux_rep] at h2
  have h3 := congrArg (fun f : ℤ →₀ W => f i) h2
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [Finset.sum_ite_eq' s i (fun n => g n), if_pos hi] at h3
  exact h3

theorem mk_X_pow_mul_X_pow (a b : ℕ) :
    mk t (X 0) ^ a * mk t (X 1) ^ b
      = t ^ min a b • MvPolynomial.CrossingQuotient.monomial t ((a : ℤ) - b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Nat.min_eq_left hab, pow_add, ← mul_assoc, ← mul_pow, mk_X_mul_mk_X, ← map_pow, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    congr 1
    rw [show ((a : ℤ) - ((a + c : ℕ) : ℤ)) = -(c : ℤ) by push_cast; ring, monomial_neg_natCast]
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Nat.min_eq_right hab, pow_add, mul_assoc, mul_comm (mk t (X 0) ^ c), ← mul_assoc, ← mul_pow, mk_X_mul_mk_X,
      ← map_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    congr 1
    rw [show (((b + c : ℕ) : ℤ) - (b : ℤ)) = (c : ℤ) by push_cast; ring, monomial_natCast]

theorem mk_monomial_mem_span (d : Fin 2 →₀ ℕ) (c : W) :
    mk t (MvPolynomial.monomial d c)
      ∈ Submodule.span W (Set.range (MvPolynomial.CrossingQuotient.monomial t)) := by
  have h : MvPolynomial.monomial d c = C c * (X 0 ^ d 0 * X 1 ^ d 1) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  rw [h, MvPolynomial.C_mul', map_smul, map_mul, map_pow, map_pow, mk_X_pow_mul_X_pow, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem span_monomial_eq_top :
    Submodule.span W (Set.range (MvPolynomial.CrossingQuotient.monomial t)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  obtain ⟨p, rfl⟩ := mk_surjective t z
  induction p using MvPolynomial.induction_on' with
  | monomial d c => exact mk_monomial_mem_span t d c
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq

end L9Core

end

theorem solution
    {W : Type*} [CommRing W] (t : W) :
    LinearIndependent W (MvPolynomial.CrossingQuotient.monomial t) ∧
      Submodule.span W (Set.range (MvPolynomial.CrossingQuotient.monomial t)) = ⊤ :=
  ⟨L9Core.linearIndependent_monomial t, L9Core.span_monomial_eq_top t⟩

end S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top (solution)
