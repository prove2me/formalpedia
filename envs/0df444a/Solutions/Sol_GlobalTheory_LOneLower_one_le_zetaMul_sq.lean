-- Prove2me | solution 1 for GlobalTheory.LOneLower.one_le_zetaMul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:09.853039+00:00
-- url     : https://prove2.me/submissions/e5683e7c-232b-4b87-9428-5ea03bd73902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {m : ℕ}
    (hm : m ≠ 0) : 1 ≤ zetaMul χ (m ^ 2) := by
  have hp : ∀ p k : ℕ, p.Prime → 1 ≤ zetaMul χ (p ^ (2 * k)) := by
    intro p k hp
    rw [zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    simp only [toArithmeticFunction, coe_mk, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
      Nat.cast_pow, map_pow]
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
    · rw [Finset.sum_range_succ', pow_zero]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by simp [h])
    · rw [Finset.sum_range_succ', pow_zero]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by simp [h])
    · simp [h, neg_one_geom_sum]
  rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hm)]
  refine Finset.prod_induction _ (fun z : ℂ => 1 ≤ z) (fun a b ha hb => ?_) le_rfl fun p hp' => ?_
  · exact one_le_mul_of_one_le_of_one_le ha hb
  · have := hp p (m.factorization p) (Nat.prime_of_mem_primeFactors hp')
    simpa [Nat.factorization_pow] using this
end GlobalTheory.LOneLower
