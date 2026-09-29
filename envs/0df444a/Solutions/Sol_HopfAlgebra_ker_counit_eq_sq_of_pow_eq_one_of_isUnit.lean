-- Prove2me | solution 1 for HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4fcda5f2-c5b6-59c0-af42-61353894db16

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit

universe u v

set_option autoImplicit false

open TensorProduct

namespace HopfAlgebra
p2m_open "HopfAlgebra"

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

theorem comul_eq_tmul_one_add_one_tmul_add_sum (x : H) {ιr : Type*} (r : Coalgebra.Repr R x ιr)
    (hx : Coalgebra.counit (R := R) x = 0) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x +
      ∑ i ∈ r.index, (r.left i - algebraMap R H (Coalgebra.counit (r.left i))) ⊗ₜ[R]
        (r.right i - algebraMap R H (Coalgebra.counit (r.right i))) := by
  have h1 : ∑ i ∈ r.index, r.left i ⊗ₜ[R] r.right i = Coalgebra.comul x := r.eq
  have h2 : ∑ i ∈ r.index, algebraMap R H (Coalgebra.counit (r.left i)) ⊗ₜ[R] r.right i
      = (1 : H) ⊗ₜ[R] x := by
    have h := congrArg (LinearMap.rTensor H (Algebra.linearMap R H)) (Coalgebra.sum_counit_tmul_eq r)
    simpa only [map_sum, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one] using h
  have h3 : ∑ i ∈ r.index, r.left i ⊗ₜ[R] algebraMap R H (Coalgebra.counit (r.right i))
      = x ⊗ₜ[R] (1 : H) := by
    have h := congrArg (LinearMap.lTensor H (Algebra.linearMap R H)) (Coalgebra.sum_tmul_counit_eq r)
    simpa only [map_sum, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one] using h
  have h4 : ∑ i ∈ r.index, algebraMap R H (Coalgebra.counit (r.left i)) ⊗ₜ[R]
      algebraMap R H (Coalgebra.counit (r.right i)) = 0 := by
    have hε : ∑ i ∈ r.index, Coalgebra.counit (R := R) (r.left i) * Coalgebra.counit (r.right i)
        = Coalgebra.counit (R := R) x := by
      conv_rhs => rw [← Coalgebra.sum_counit_smul r]
      simp only [map_sum, map_smul, smul_eq_mul]
    calc ∑ i ∈ r.index, algebraMap R H (Coalgebra.counit (r.left i)) ⊗ₜ[R]
            algebraMap R H (Coalgebra.counit (r.right i))
          = ∑ i ∈ r.index, (Coalgebra.counit (R := R) (r.left i) * Coalgebra.counit (r.right i)) •
              ((1 : H) ⊗ₜ[R] (1 : H)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul_smul,
              mul_comm]
      _ = 0 := by rw [← Finset.sum_smul, hε, hx, zero_smul]
  simp only [sub_tmul, tmul_sub, Finset.sum_sub_distrib, h1, h2, h3, h4]
  abel

theorem ofConv_toConv_pow_apply_of_counit_eq_zero
    {T : Type v} [CommRing T] [Algebra R T] (π : H →ₐ[R] T)
    (hprod : ∀ a b : H, Coalgebra.counit (R := R) a = 0 → Coalgebra.counit (R := R) b = 0 →
      π a * π b = 0)
    (k : ℕ) (x : H) (hx : Coalgebra.counit (R := R) x = 0) :
    (WithConv.ofConv ((WithConv.toConv π : WithConv (H →ₐ[R] T)) ^ k)) x = (k : T) * π x := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, AlgHom.convOne_apply, hx, map_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, AlgHom.convMul_apply,
      comul_eq_tmul_one_add_one_tmul_add_sum x (Coalgebra.Repr.arbitrary R x) hx]
    simp only [map_add, map_sum, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
    have hvan : ∀ i ∈ (Coalgebra.Repr.arbitrary R x).index,
        (WithConv.ofConv ((WithConv.toConv π : WithConv (H →ₐ[R] T)) ^ k))
            ((Coalgebra.Repr.arbitrary R x).left i -
              algebraMap R H (Coalgebra.counit ((Coalgebra.Repr.arbitrary R x).left i))) *
          π ((Coalgebra.Repr.arbitrary R x).right i -
              algebraMap R H (Coalgebra.counit ((Coalgebra.Repr.arbitrary R x).right i))) = 0 := by
      intro i _
      have ha : Coalgebra.counit (R := R) ((Coalgebra.Repr.arbitrary R x).left i -
          algebraMap R H (Coalgebra.counit ((Coalgebra.Repr.arbitrary R x).left i))) = 0 := by
        rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
      have hb : Coalgebra.counit (R := R) ((Coalgebra.Repr.arbitrary R x).right i -
          algebraMap R H (Coalgebra.counit ((Coalgebra.Repr.arbitrary R x).right i))) = 0 := by
        rw [map_sub, Bialgebra.counit_algebraMap, sub_self]
      rw [ih _ ha, mul_assoc, hprod _ _ ha hb, mul_zero]
    rw [Finset.sum_eq_zero hvan, add_zero, ih x hx, Nat.cast_succ]
    ring

end HopfAlgebra

open TensorProduct in

theorem solution
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2 := by
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom R H) with hI
  refine le_antisymm ?_ (Ideal.pow_le_self two_ne_zero)
  intro x hx
  have hx0 : Coalgebra.counit (R := R) x = 0 := by
    rwa [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hx

  have hprod : ∀ a b : H, Coalgebra.counit (R := R) a = 0 → Coalgebra.counit (R := R) b = 0 →
      Ideal.Quotient.mkₐ R (I ^ 2) a * Ideal.Quotient.mkₐ R (I ^ 2) b = 0 := fun a b ha hb => by
    rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    refine Ideal.mul_mem_mul ?_ ?_
    · rw [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]; exact ha
    · rw [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]; exact hb
  have key := HopfAlgebra.ofConv_toConv_pow_apply_of_counit_eq_zero (R := R) (Ideal.Quotient.mkₐ R (I ^ 2))
    hprod n x hx0
  rw [hH (H ⧸ I ^ 2) _, AlgHom.convOne_apply, hx0, map_zero] at key

  have hu : IsUnit ((n : H ⧸ I ^ 2)) := by
    rw [← map_natCast (algebraMap R (H ⧸ I ^ 2))]
    exact hn.map _
  have hπ : Ideal.Quotient.mkₐ R (I ^ 2) x = 0 := (hu.mul_right_eq_zero).mp key.symm
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hπ

end S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit
end P2MW
export P2MW.S_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit (solution)
