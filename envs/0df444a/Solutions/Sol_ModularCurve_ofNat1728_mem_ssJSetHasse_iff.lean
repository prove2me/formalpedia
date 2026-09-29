-- Prove2me | solution 1 for ModularCurve.ofNat1728_mem_ssJSetHasse_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/16127190-cefa-540d-bb43-aea99e4604a1

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff

set_option autoImplicit false

p2m_open "Polynomial P2MW.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff.Polynomial"

noncomputable section

namespace Polynomial
p2m_export "Polynomial" "C X coeff C_pow coeff_mul_C coeff_mul_X_pow coeff_C_mul finsetSum_coeff coeff_X_pow ring"
p2m_open "Polynomial"

theorem coeff_C_mul_X_pow_add_C_pow' {R : Type*} [CommRing R] (a b : R) (d m n : ℕ) :
    ((C a * X ^ d + C b) ^ m).coeff n
      = ∑ k ∈ Finset.range (m + 1), if n = d * k then a ^ k * b ^ (m - k) * (m.choose k) else 0 := by
  rw [add_pow, finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, ← C_pow, ← C_pow, ← pow_mul, ← map_natCast C, coeff_mul_C, coeff_mul_C,
    coeff_C_mul, coeff_X_pow]
  split_ifs <;> ring

end Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "b₂ twoTorsionPolynomial coe_Δ' exists_variableChange_of_j_eq ofJ1728_Δ ofJ1728 ofJ1728_c₄ b₆ VariableChange j b₄ hasseInvariant hasseInvariant_variableChange"
p2m_open "WeierstrassCurve"

theorem hasseInvariant_variableChange_eq_zero_iff' {K : Type*} [Field K] {q : ℕ} [Fact q.Prime]
    [CharP K q] (W : WeierstrassCurve K) (v : VariableChange K) :
    (v • W).hasseInvariant q = 0 ↔ W.hasseInvariant q = 0 := by
  rw [hasseInvariant_variableChange, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ (v.u⁻¹).ne_zero

end WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "ssJSetHasse"
p2m_open "ModularCurve"

p2m_open "WeierstrassCurve P2MW.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff.WeierstrassCurve"

theorem two_ne_zero_of_charP_of_ne_two' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime]
    [CharP K q] (hq2 : q ≠ 2) : (2 : K) ≠ 0 := by
  have : ((2 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K q]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem natCast_choose_ne_zero_of_lt' (K : Type*) [Field K] {q : ℕ} [hp : Fact q.Prime] [CharP K q]
    {m k : ℕ} (hm : m < q) (hk : k ≤ m) : ((m.choose k : ℕ) : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K q]
  intro hd
  have h1 : m.choose k ∣ m.factorial :=
    ⟨k.factorial * (m - k).factorial, by rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial hk]⟩
  have := (hp.out.dvd_factorial).mp (hd.trans h1)
  omega

theorem mem_ssJSetHasse_iff_of_j_eq' {K : Type*} [Field K] [IsAlgClosed K] (q : ℕ) [Fact q.Prime]
    [CharP K q] (W : WeierstrassCurve K) [W.IsElliptic] {j : K} (hW : W.j = j) :
    j ∈ ssJSetHasse q K ↔ W.hasseInvariant q = 0 := by
  constructor
  · intro h
    exact h W hW
  · intro h
    rw [ssJSetHasse, Set.mem_setOf_eq]
    intro W' _ hW'
    haveI := IsSepClosed.of_isAlgClosed K
    obtain ⟨v, rfl⟩ := exists_variableChange_of_j_eq W W' (by rw [hW, hW'])
    rwa [hasseInvariant_variableChange_eq_zero_iff']

theorem twoTorsionPolynomial_ofJ1728_toPoly' (K : Type*) [Field K] :
    (ofJ1728 K).twoTorsionPolynomial.toPoly = (C 4 * X ^ 2 + C 4) * X ^ 1 := by
  have hb2 : (ofJ1728 K).b₂ = 0 := by simp [ofJ1728, b₂]
  have hb4 : (ofJ1728 K).b₄ = 2 := by simp [ofJ1728, b₄]
  have hb6 : (ofJ1728 K).b₆ = 0 := by simp [ofJ1728, b₆]
  simp only [twoTorsionPolynomial, Cubic.toPoly, hb2, hb4, hb6, map_zero, zero_mul, add_zero]
  rw [show (2 : K) * 2 = 4 by norm_num]
  ring

theorem hasseInvariant_ofJ1728_eq_zero_iff' (K : Type*) [Field K] (q : ℕ) [hp : Fact q.Prime]
    [CharP K q] (hq2 : q ≠ 2) :
    (ofJ1728 K).hasseInvariant q = 0 ↔ ¬ 2 ∣ (q - 1) / 2 := by
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hq2
  have hm1 : (q - 1) / 2 = m := by omega
  have hm2 : q - 1 = m + m := by omega
  have hmq : m < q := by omega
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero _ (two_ne_zero_of_charP_of_ne_two' K hq2)
  rw [hasseInvariant, hm1, hm2, twoTorsionPolynomial_ofJ1728_toPoly', mul_pow, ← pow_mul, one_mul,
    coeff_mul_X_pow, coeff_C_mul_X_pow_add_C_pow']
  by_cases h2 : 2 ∣ m
  · obtain ⟨a, rfl⟩ := h2
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]
      refine iff_of_false ?_ (fun h => h (dvd_mul_right 2 a))
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h4))
        (natCast_choose_ne_zero_of_lt' K hmq (by omega))
    · intro k _ hk
      exact if_neg (by omega)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Finset.sum_eq_zero (fun k _ => if_neg (by omega))]
    exact iff_of_true rfl h2

theorem isElliptic_ofJ1728_of_two_ne_zero' (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    (ofJ1728 K).IsElliptic := by
  refine ⟨?_⟩
  rw [ofJ1728_Δ, isUnit_iff_ne_zero, neg_ne_zero, show (64 : K) = 2 ^ 6 by norm_num]
  exact pow_ne_zero _ h2

theorem ofNat1728_mem_ssJSetHasse_iff' (q : ℕ) [hp : Fact q.Prime] (hq : 5 ≤ q) (K : Type*)
    [Field K] [IsAlgClosed K] [CharP K q] : (1728 : K) ∈ ssJSetHasse q K ↔ q % 4 = 3 := by
  have hq2 : q ≠ 2 := by omega
  have h2 := two_ne_zero_of_charP_of_ne_two' K hq2
  haveI := isElliptic_ofJ1728_of_two_ne_zero' K h2
  have h64 : (64 : K) ≠ 0 := by
    rw [show (64 : K) = 2 ^ 6 by norm_num]; exact pow_ne_zero _ h2
  have hj : (ofJ1728 K).j = 1728 := by
    rw [j, Units.val_inv_eq_inv_val, coe_Δ', ofJ1728_Δ, ofJ1728_c₄, inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr h64)]
    norm_num
  rw [mem_ssJSetHasse_iff_of_j_eq' q (ofJ1728 K) hj, hasseInvariant_ofJ1728_eq_zero_iff' K q hq2]
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hq2
  have hm1 : (q - 1) / 2 = m := by omega
  rw [hm1]
  omega

end ModularCurve

end

p2m_open "ModularCurve P2MW.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff.ModularCurve"

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*)
    [Field K] [IsAlgClosed K] [CharP K q] : (1728 : K) ∈ ssJSetHasse q K ↔ q % 4 = 3 :=
  ModularCurve.ofNat1728_mem_ssJSetHasse_iff' q hq K

end S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff
end P2MW
export P2MW.S_ModularCurve_ofNat1728_mem_ssJSetHasse_iff (solution)
