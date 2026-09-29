-- Prove2me | solution 1 for Ideal.isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/55d8d60a-acea-586b-a10b-313e6e341862

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero

set_option autoImplicit false

namespace CrtSplitAux

open Polynomial

variable {A : Type} [CommRing A] [IsDomain A]

theorem isUnit_one_sub {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓA : IsUnit ((ℓ : ℕ) : A))
    {ν : A} (hν : IsPrimitiveRoot ν ℓ) : IsUnit (1 - ν) := by
  have hpos : 0 < ℓ := hℓ.out.pos
  have h1 : Polynomial.eval 1 (Polynomial.cyclotomic ℓ A) = (ℓ : A) := Polynomial.eval_one_cyclotomic_prime
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hν, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  have hmem : ν ∈ primitiveRoots ℓ A := (mem_primitiveRoots hpos).mpr hν
  have hprod : IsUnit (∏ μ ∈ primitiveRoots ℓ A, ((1 : A) - μ)) := by rw [h1]; exact hℓA
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun μ => (1 : A) - μ) hmem) hprod

theorem isUnit_sub {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓA : IsUnit ((ℓ : ℕ) : A))
    {a μ : A} (ha : IsPrimitiveRoot a ℓ) (hμ : IsPrimitiveRoot μ ℓ) (h : μ ≠ a) : IsUnit (μ - a) := by
  have hpos : 0 < ℓ := hℓ.out.pos
  have haℓ : a ^ ℓ = 1 := ha.pow_eq_one
  have hμℓ : μ ^ ℓ = 1 := hμ.pow_eq_one
  have hsucc : a ^ (ℓ - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel hpos, haℓ]
  set ν : A := μ * a ^ (ℓ - 1) with hν
  have hνℓ : ν ^ ℓ = 1 := by
    rw [hν, mul_pow, ← pow_mul, hμℓ, one_mul, mul_comm, pow_mul, haℓ, one_pow]
  have hν1 : ν ≠ 1 := by
    intro h1
    apply h
    calc μ = μ * (a ^ (ℓ - 1) * a) := by rw [hsucc, mul_one]
      _ = ν * a := by rw [hν, mul_assoc]
      _ = a := by rw [h1, one_mul]
  have hνP : IsPrimitiveRoot ν ℓ := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hνℓ hν1)
  have hu : IsUnit (1 - ν) := isUnit_one_sub hℓA hνP
  have hau : IsUnit a := ha.isUnit hpos.ne'
  have hrew : μ - a = -(a * (1 - ν)) := by
    rw [mul_sub, mul_one, hν, mul_comm μ, ← mul_assoc, mul_comm a, hsucc, one_mul, neg_sub]
  rw [hrew]
  exact (hau.mul hu).neg

end CrtSplitAux

open CrtSplitAux

open Polynomial Classical in

theorem solution
    (A : Type) [CommRing A] [IsDomain A] (B : Type) [CommRing B] [Algebra A B]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓA : IsUnit ((ℓ : ℕ) : A)) (hω : ∃ ω : A, IsPrimitiveRoot ω ℓ)
    (ξ : B) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A) = 0)
    (a : A) (ha : a ^ ℓ = 1) (ha1 : a ≠ 1) :
    IsCompl (Ideal.span {ξ - algebraMap A B a})
      (Ideal.span {∏ μ ∈ (primitiveRoots ℓ A).erase a, (ξ - algebraMap A B μ)}) := by
  have hprime : ℓ.Prime := Fact.out
  have hpos : 0 < ℓ := hprime.pos
  obtain ⟨ω, hω⟩ := hω
  have haP : IsPrimitiveRoot a ℓ := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime ha ha1)
  have haMem : a ∈ primitiveRoots ℓ A := (mem_primitiveRoots hpos).mpr haP

  have hall : ∏ μ ∈ primitiveRoots ℓ A, (ξ - algebraMap A B μ) = 0 := by
    have h := hξ
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hω, map_prod] at h
    simpa only [map_sub, aeval_X, aeval_C] using h
  have hxy : (ξ - algebraMap A B a) * ∏ μ ∈ (primitiveRoots ℓ A).erase a, (ξ - algebraMap A B μ) = 0 := by
    rw [Finset.mul_prod_erase (primitiveRoots ℓ A) (fun μ => ξ - algebraMap A B μ) haMem]
    exact hall

  have hcop : IsCoprime (ξ - algebraMap A B a) (∏ μ ∈ (primitiveRoots ℓ A).erase a, (ξ - algebraMap A B μ)) := by
    apply IsCoprime.prod_right
    intro μ hμ
    obtain ⟨hμa, hμmem⟩ := Finset.mem_erase.mp hμ
    have hu : IsUnit (μ - a) := isUnit_sub hℓA haP ((mem_primitiveRoots hpos).mp hμmem) hμa
    obtain ⟨d, hd⟩ := (hu.map (algebraMap A B))
    refine ⟨↑d⁻¹, -↑d⁻¹, ?_⟩
    have hdiff : (ξ - algebraMap A B a) - (ξ - algebraMap A B μ) = (d : B) := by
      rw [hd, map_sub]; ring
    calc ↑d⁻¹ * (ξ - algebraMap A B a) + -↑d⁻¹ * (ξ - algebraMap A B μ)
        = ↑d⁻¹ * ((ξ - algebraMap A B a) - (ξ - algebraMap A B μ)) := by ring
      _ = 1 := by rw [hdiff, Units.inv_mul]
  have hI : IsCoprime (Ideal.span {ξ - algebraMap A B a})
      (Ideal.span {∏ μ ∈ (primitiveRoots ℓ A).erase a, (ξ - algebraMap A B μ)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hcop
  refine IsCompl.of_eq ?_ (Ideal.isCoprime_iff_sup_eq.mp hI)
  rw [← Ideal.mul_eq_inf_of_isCoprime hI, Ideal.span_singleton_mul_span_singleton, hxy]
  simp

end S_Ideal_isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero
end P2MW
export P2MW.S_Ideal_isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero (solution)
