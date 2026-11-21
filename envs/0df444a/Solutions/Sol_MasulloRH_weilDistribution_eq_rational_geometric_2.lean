-- Prove2me | solution 2 for MasulloRH.weilDistribution_eq_rational_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:28:55.051066+00:00
-- url     : https://prove2.me/submissions/32f580c1-4540-47c5-b785-561fbda20b0b

import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Mathlib.Data.Nat.Factorization.PrimePow

set_option autoImplicit false

open Set MeasureTheory MasulloRH

private theorem log_mellin (φ : ℝ → ℂ) (z : ℂ) :
    ConnesRZ.mellinHat (φ ∘ Real.exp) z = mellin φ (z - 1/2) := by
  unfold ConnesRZ.mellinHat mellin
  rw [← Real.range_exp, ← image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, abs_of_pos (Real.exp_pos x), smul_eq_mul,
    Complex.real_smul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (φ (Real.exp x))]
  congr 2
  ring

private theorem prime_reindex (φ : ℝ → ℂ) :
    ConnesRZ.primeSum (φ ∘ Real.exp) = ∑' i, primePowerTraceTerm φ i := by
  let idx (i : Nat.Primes × ℕ) : ℕ := Nat.Primes.prodNatEquiv i
  have hi : Function.Injective idx := Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective
  unfold ConnesRZ.primeSum
  rw [← hi.tsum_eq]
  · apply tsum_congr
    rintro ⟨p,k⟩
    have hm : 0 < ((p : ℕ) : ℝ) ^ (k+1) := pow_pos (by exact_mod_cast p.prop.pos) _
    simp [-Real.log_pow, idx, primePowerTraceTerm, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
      ArithmeticFunction.vonMangoldt_apply_prime p.prop, Real.exp_neg, Real.exp_log hm]
  · intro m hm
    by_contra hn
    have h : ¬ IsPrimePow m := fun h => hn ⟨Nat.Primes.prodNatEquiv.symm ⟨m,h⟩,
      congrArg Subtype.val (Nat.Primes.prodNatEquiv.apply_symm_apply _)⟩
    exact hm (by simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h])


theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ConnesRZ.weilDistribution (fun u => φ (Real.exp u)) =
      (mellin φ (1/2) + mellin φ (-1/2)) -
        ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
          ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) := by
  change ConnesRZ.weilDistribution (φ ∘ Real.exp) = _
  rw [ConnesRZ.weilDistribution, log_mellin φ 0, log_mellin φ 1, prime_reindex,
    archTerm_log_test_eq_neg_real_place φ hφ]
  rw [show (0:ℂ)-1/2 = -1/2 by ring, show (1:ℂ)-1/2 = 1/2 by ring]
  ring
