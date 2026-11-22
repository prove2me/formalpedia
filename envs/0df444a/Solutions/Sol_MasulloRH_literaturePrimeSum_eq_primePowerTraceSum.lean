-- Prove2me | solution 1 for MasulloRH.literaturePrimeSum_eq_primePowerTraceSum
-- status  : ACCEPTED   (prove)
-- author  : @cyw
-- created : 2026-11-20T23:01:10.90323+00:00
-- url     : https://prove2.me/submissions/123d7acf-d4c4-406d-ba03-11d402c8b235

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped ArithmeticFunction.vonMangoldt

theorem solution (φ : ℝ → ℂ) :
    (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
      (φ (Real.exp (Real.log n)) + φ (Real.exp (-Real.log n)))) =
      ∑' i : Nat.Primes × ℕ, MasulloRH.primePowerTraceTerm φ i := by
  let f : ℕ → ℂ := fun n =>
    ((Λ n / Real.sqrt n : ℝ) : ℂ) * (φ n + φ (n : ℝ)⁻¹)
  have hs : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hpow
    exact hn (by simp [f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow])
  calc
    _ = ∑' n : ℕ, f n := by
      refine tsum_congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [f]
      · simp [f, Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr hn)]
    _ = ∑' n : {n : ℕ // IsPrimePow n}, f n.val :=
      (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' i : Nat.Primes × ℕ, f (Nat.Primes.prodNatEquiv i).val :=
      (Nat.Primes.prodNatEquiv.tsum_eq _).symm
    _ = _ := by
      refine tsum_congr fun ⟨p, k⟩ => ?_
      simp [f, MasulloRH.primePowerTraceTerm,
        ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
        ArithmeticFunction.vonMangoldt_apply_prime p.property]
