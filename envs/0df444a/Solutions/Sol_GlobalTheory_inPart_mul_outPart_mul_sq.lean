-- Prove2me | solution 1 for GlobalTheory.inPart_mul_outPart_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:42.250303+00:00
-- url     : https://prove2.me/submissions/ddae5238-82b5-40d3-9f60-36d1584b500a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_InPartMulOutPartMulSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution (m₀ m : ℕ) (hm : 0 < m) :
    inPart m₀ m * outPart m₀ m * (∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)) ^ 2 = m := by
  unfold inPart outPart
  rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hm.ne']
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul]
  rcases Nat.even_or_odd' (m.factorization p) with ⟨k, hk | hk⟩
  · have h1 : ¬ Odd (m.factorization p) := by
      rw [hk]; simp
    have h2 : m.factorization p / 2 * 2 = m.factorization p := by omega
    rw [if_neg (fun h => h1 h.2), if_neg (fun h => h1 h.2), h2]
    ring
  · have h1 : Odd (m.factorization p) := ⟨k, hk⟩
    have h2 : m.factorization p = m.factorization p / 2 * 2 + 1 := by omega
    by_cases hp : p ∣ m₀
    · rw [if_pos ⟨hp, h1⟩, if_neg (fun h => h.1 hp)]
      conv_rhs => rw [h2]
      ring
    · rw [if_neg (fun h => hp h.1), if_pos ⟨hp, h1⟩]
      conv_rhs => rw [h2]
      ring
end GlobalTheory
