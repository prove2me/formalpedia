-- Prove2me | solution 1 for GlobalTheory.exists_integer_generator_of_sq_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:32.620378+00:00
-- url     : https://prove2.me/submissions/72a14c6f-62f0-43a3-9406-ebab8784ae7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module
namespace GlobalTheory
open QuadraticZeta
private theorem norm_sq_add_norm_sq_sub_eq_complete_square {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (h2 : finrank ℚ K = 2) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -d) :
    (∀ x : K, ∃ a b : ℚ, x = a + b * r) ∧ ∃ τ : K →+* K, τ r = -r := by
  have hli : LinearIndependent ℚ ![(1 : K), r] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      have htK : (t : K) ≠ 0 := Rat.cast_ne_zero.mpr ht
      have hr' : r = ((-s / t : ℚ) : K) := by
        push_cast
        field_simp
        linear_combination hst
      have h0 : (((-s / t) ^ 2 + d : ℚ) : K) = 0 := by
        rw [Rat.cast_add, Rat.cast_pow, ← hr', hr]
        push_cast
        ring
      have h0' : (-s / t) ^ 2 + (d : ℚ) = 0 := by exact_mod_cast h0
      have hdpos : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
      nlinarith [sq_nonneg (-s / t)]
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = r := by simp [B]
  have hdec : ∀ x : K, ∃ a b : ℚ, x = a + b * r := by
    intro x
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    rw [Fin.sum_univ_two, hB0, hB1, Rat.smul_def, Rat.smul_def, mul_one]
  refine ⟨hdec, ?_⟩
  have hf : ∀ a b : ℚ, (B.constr ℚ ![(1 : K), -r]) ((a : K) + b * r) = a - b * r := by
    intro a b
    have e : ((a : K) + b * r) = a • B 0 + b • B 1 := by
      rw [hB0, hB1, Rat.smul_def, Rat.smul_def, mul_one]
    rw [e, map_add, map_smul, map_smul, Basis.constr_basis, Basis.constr_basis]
    simp [Rat.smul_def, sub_eq_add_neg]
  have hone : (B.constr ℚ ![(1 : K), -r]) 1 = 1 := by simpa using hf 1 0
  have hmul : ∀ x y : K, (B.constr ℚ ![(1 : K), -r]) (x * y) =
      (B.constr ℚ ![(1 : K), -r]) x * (B.constr ℚ ![(1 : K), -r]) y := by
    intro x y
    obtain ⟨a, b, rfl⟩ := hdec x
    obtain ⟨c, e, rfl⟩ := hdec y
    have hxy : ((a : K) + b * r) * (c + e * r) =
        ((a * c - d * b * e : ℚ) : K) + ((a * e + b * c : ℚ) : K) * r := by
      push_cast
      linear_combination ((b : K) * e) * hr
    rw [hxy, hf, hf, hf]
    push_cast
    linear_combination (-((b : K) * e)) * hr
  exact ⟨(AlgHom.ofLinearMap (B.constr ℚ ![(1 : K), -r]) hone hmul).toRingHom,
    by show (B.constr ℚ ![(1 : K), -r]) r = -r; simpa using hf 0 1⟩
private theorem exists_int_eq_of_isIntegral_rat {K : Type*} [Field K] [CharZero K] (q : ℚ)
    (h : IsIntegral ℤ (q : K)) : ∃ z : ℤ, q = z := by
  have hq : IsIntegral ℤ q :=
    (isIntegral_algHom_iff (algebraMap ℚ K).toIntAlgHom (algebraMap ℚ K).injective).mp h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  exact ⟨z, by simpa using hz.symm⟩
private theorem exists_int_eq_of_squarefree_mul_sq_eq_int {d : ℕ} (hsq : Squarefree d) (q : ℚ) (M : ℤ)
    (h : (d : ℚ) * q ^ 2 = M) : ∃ z : ℤ, q = z := by
  have hden : q.den = 1 := by
    have hq := Rat.num_div_den q
    have hpos : (q.den : ℚ) ≠ 0 := by positivity
    have key : (d : ℤ) * q.num ^ 2 = M * q.den ^ 2 := by
      have h' : (d : ℚ) * ((q.num : ℚ) / q.den) ^ 2 = M := by rw [hq]; exact h
      field_simp at h'
      have h'' : (d : ℤ) * q.num ^ 2 = ((q.den ^ 2 : ℕ) : ℤ) * M := by exact_mod_cast h'
      push_cast at h''
      linear_combination h''
    have key' : d * q.num.natAbs ^ 2 = M.natAbs * q.den ^ 2 := by
      have := congrArg Int.natAbs key
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    have hdvd : q.den ^ 2 ∣ d * q.num.natAbs ^ 2 := ⟨M.natAbs, by rw [key']; ring⟩
    have hcop : Nat.Coprime (q.den ^ 2) (q.num.natAbs ^ 2) := Nat.Coprime.pow 2 2 q.reduced.symm
    have h3 : q.den ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right hdvd
    have hu := hsq q.den (by simpa [sq] using h3)
    simpa using hu
  exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
end GlobalTheory
end

set_option autoImplicit false
open NumberField Module
open GlobalTheory
open QuadraticZeta
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (h2 : finrank ℚ K = 2) (hsq : Squarefree d) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -d) :
    ∃ w : 𝓞 K, 2 * (w : K) = 1 + r ∧ ∀ c : 𝓞 K, ∃ m n : ℤ, c = m + n * w := by
  obtain ⟨hdec, τ, hτ⟩ := norm_sq_add_norm_sq_sub_eq_complete_square h2 hd hr
  obtain ⟨k, hk⟩ : ∃ k, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hw : IsIntegral ℤ ((1 + r) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((k : ℤ) + 1), ?_, ?_⟩
    · monicity!
    · rw [hk] at hr
      push_cast at hr
      simp
      linear_combination (1 / 4 : K) * hr
  refine ⟨⟨(1 + r) / 2, hw⟩, ?_, ?_⟩
  · show 2 * ((1 + r) / 2) = 1 + r
    ring
  · intro c
    obtain ⟨a, b, hab⟩ := hdec c
    have hc : IsIntegral ℤ (c : K) := c.2
    have hc' : IsIntegral ℤ (τ c) := map_isIntegral_int τ hc
    have hτc : τ (c : K) = a - b * r := by
      rw [hab, map_add, map_mul, map_ratCast, map_ratCast, hτ]
      ring
    have hsum : IsIntegral ℤ (((2 * a : ℚ)) : K) := by
      have h := hc.add hc'
      rw [hτc, hab] at h
      have e : ((2 * a : ℚ) : K) = ↑a + ↑b * r + (↑a - ↑b * r) := by
        push_cast
        ring
      rw [e]
      exact h
    have hprod : IsIntegral ℤ (((a ^ 2 + d * b ^ 2 : ℚ)) : K) := by
      have h := hc.mul hc'
      rw [hτc, hab] at h
      have e : ((a ^ 2 + d * b ^ 2 : ℚ) : K) = (↑a + ↑b * r) * (↑a - ↑b * r) := by
        push_cast
        linear_combination ((b : K) ^ 2) * hr
      rw [e]
      exact h
    obtain ⟨A, hA⟩ := exists_int_eq_of_isIntegral_rat _ hsum
    obtain ⟨N, hN⟩ := exists_int_eq_of_isIntegral_rat _ hprod
    obtain ⟨B, hB⟩ := exists_int_eq_of_squarefree_mul_sq_eq_int hsq (2 * b) (4 * N - A ^ 2) (by
      push_cast
      rw [← hN, ← hA]
      ring)
    have hpar : Even (A - B) := by
      have h4 : (A : ℚ) ^ 2 + d * (B : ℚ) ^ 2 = 4 * N := by
        rw [← hA, ← hB, ← hN]
        ring
      have h4' : A ^ 2 + (d : ℤ) * B ^ 2 = 4 * N := by exact_mod_cast h4
      have hdodd : Odd (d : ℤ) := ⟨2 * k + 1, by rw [hk]; push_cast; ring⟩
      have hnd : ¬ Even (d : ℤ) := Int.not_even_iff_odd.mpr hdodd
      have hev : Even (A ^ 2 + (d : ℤ) * B ^ 2) := ⟨2 * N, by rw [h4']; ring⟩
      rw [Int.even_sub]
      simpa [Int.even_add, Int.even_mul, Int.even_pow, hnd] using hev
    obtain ⟨m, hm⟩ := hpar
    refine ⟨m, B, ?_⟩
    apply RingOfIntegers.ext
    have hA' : 2 * (a : K) = A := by exact_mod_cast congrArg (fun q : ℚ => (q : K)) hA
    have hB' : 2 * (b : K) = B := by exact_mod_cast congrArg (fun q : ℚ => (q : K)) hB
    have hm' : (A : K) - B = m + m := by exact_mod_cast congrArg (fun z : ℤ => (z : K)) hm
    rw [hab]
    push_cast
    show (a : K) + b * r = m + B * ((1 + r) / 2)
    linear_combination (1 / 2 : K) * hA' + (r / 2) * hB' + (1 / 2 : K) * hm'
end GlobalTheory
