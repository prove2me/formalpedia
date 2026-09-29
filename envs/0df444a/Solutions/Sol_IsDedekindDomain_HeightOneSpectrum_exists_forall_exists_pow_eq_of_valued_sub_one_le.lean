-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/68cfbea0-5c86-596d-a3d8-b57cb0f876d8

import Mathlib
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∀ a : v.adicCompletion K,
      Valued.v (a - 1) ≤ WithZero.exp (-(m : ℤ)) → ∃ c : v.adicCompletion K, c ^ n = a := by

  have hn0 : ((n : ℕ) : v.adicCompletion K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (v.adicCompletion K)) n]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn.ne')
  have hnle : Valued.v ((n : ℕ) : v.adicCompletion K) ≤ 1 := by
    have : ((n : ℕ) : v.adicCompletion K) = (((n : ℕ) : v.adicCompletionIntegers K) : v.adicCompletion K) := by push_cast; rfl
    rw [this]; exact ((n : ℕ) : v.adicCompletionIntegers K).2
  have hvn0 : Valued.v ((n : ℕ) : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hn0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v ((n : ℕ) : v.adicCompletion K) = WithZero.exp (-(k : ℤ)) := by
    obtain ⟨z, hz⟩ : ∃ z : ℤ, Valued.v ((n : ℕ) : v.adicCompletion K) = WithZero.exp z := by
      obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hvn0
      exact ⟨Multiplicative.toAdd u, by rw [← hu]; rfl⟩
    have hz0 : z ≤ 0 := by
      rw [hz, ← WithZero.exp_zero] at hnle
      exact WithZero.exp_le_exp.mp hnle
    refine ⟨(-z).toNat, ?_⟩
    rw [hz, Int.toNat_of_nonneg (by omega), neg_neg]
  refine ⟨2 * k + 1, fun a ha => ?_⟩

  have ha1 : Valued.v a ≤ 1 := by
    have : a = (a - 1) + 1 := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le (ha.trans ?_) (le_of_eq (map_one _)))
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)
  set aO : v.adicCompletionIntegers K := ⟨a, ha1⟩ with haO
  set f : Polynomial ↥(v.adicCompletionIntegers K) := Polynomial.X ^ n - Polynomial.C aO with hf
  have hf1 : ((f.eval 1 : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) = 1 - a := by
    rw [hf, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow]; rfl
  have hf2 : ((f.derivative.eval 1 : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) = (n : ℕ) := by
    rw [hf, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_X_pow, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, Polynomial.eval_C]
    push_cast; rfl
  have hlt : Valued.v ((f.eval 1 : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) <
      Valued.v ((f.derivative.eval 1 : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ^ 2 := by
    rw [hf1, hf2, hk, ← WithZero.exp_nsmul, Valuation.map_sub_swap]
    refine lt_of_le_of_lt ha ?_
    rw [WithZero.exp_lt_exp]
    simp only [nsmul_eq_mul]
    push_cast; omega
  obtain ⟨c, hc, -⟩ := IsDedekindDomain.HeightOneSpectrum.exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt K v f 1 hlt
  refine ⟨(c : v.adicCompletion K), ?_⟩
  have := congrArg (fun z : ↥(v.adicCompletionIntegers K) => (z : v.adicCompletion K)) hc.eq_zero
  simp only [hf, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
  rw [show ((c ^ n - aO : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) = (c : v.adicCompletion K) ^ n - a from rfl] at this
  exact sub_eq_zero.mp (this.trans rfl)

end S_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le (solution)
