-- Prove2me | solution 1 for IsPrimitiveRoot.exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/54ec1c19-8932-51c8-b0cd-b1afdb8faa79

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsPrimitiveRoot_exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul

set_option autoImplicit false

open IsLocalRing

theorem solution
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (ζ : A) (hζ : IsPrimitiveRoot ζ q)
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε)
    (hϖq : ϖ ^ (q - 1) = ε * (q : A)) :
    ∃ u : A, IsUnit u ∧ 1 - ζ = u * ϖ := by
  classical
  have hqp : q.Prime := Fact.out
  have hq1 : 1 < q := hqp.one_lt
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ

  have hassoc : ∀ μ ∈ primitiveRoots q A, Associated (1 - ζ) (1 - μ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ q := isPrimitiveRoot_of_mem_primitiveRoots hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply associated_of_dvd_dvd
    · exact ⟨∑ k ∈ Finset.range i, ζ ^ k, (mul_neg_geom_sum ζ i).symm⟩
    · refine ⟨∑ k ∈ Finset.range j, (ζ ^ i) ^ k, ?_⟩
      rw [mul_neg_geom_sum, hj]

  have hprod : ∏ μ ∈ primitiveRoots q A, (1 - μ) = (q : A) := by
    have h := congrArg (Polynomial.eval (1 : A)) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at h
    simpa using h.symm
  have hcard : (primitiveRoots q A).card = q - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hqp]

  have hassoc2 : Associated ((1 - ζ) ^ (q - 1)) (q : A) := by
    rw [← hprod, ← hcard, ← Finset.prod_const]
    apply associated_of_dvd_dvd
    · exact Finset.prod_dvd_prod_of_dvd _ _ (fun μ hμ => (hassoc μ hμ).dvd)
    · exact Finset.prod_dvd_prod_of_dvd _ _ (fun μ hμ => (hassoc μ hμ).symm.dvd)

  have hne : (1 : A) - ζ ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hq1).symm
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr
  obtain ⟨w, hw⟩ := hassoc2

  have key : ((u ^ (q - 1) * w : Aˣ) : A) * ϖ ^ (k * (q - 1)) = ((hε.unit⁻¹ : Aˣ) : A) * ϖ ^ (q - 1) := by
    have h1 : ((u ^ (q - 1) * w : Aˣ) : A) * ϖ ^ (k * (q - 1)) = (1 - ζ) ^ (q - 1) * ↑w := by
      rw [hk, mul_pow, ← pow_mul, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have h2 : ((hε.unit⁻¹ : Aˣ) : A) * ϖ ^ (q - 1) = (q : A) := by
      rw [hϖq, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [h1, h2, hw]
  have hkq : k * (q - 1) = q - 1 :=
    IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr _ _ _ _ key
  have hk1 : k = 1 := by
    have hpos : 0 < q - 1 := by omega
    have : k * (q - 1) = 1 * (q - 1) := by rw [hkq, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  refine ⟨u, u.isUnit, ?_⟩
  rw [hk, hk1, pow_one]

end S_IsPrimitiveRoot_exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul
end P2MW
export P2MW.S_IsPrimitiveRoot_exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul (solution)
