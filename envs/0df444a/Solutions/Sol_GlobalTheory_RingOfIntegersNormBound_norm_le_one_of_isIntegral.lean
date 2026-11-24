-- Prove2me | solution 1 for GlobalTheory.RingOfIntegersNormBound.norm_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:06.294695+00:00
-- url     : https://prove2.me/submissions/f73398a2-6e79-4d8a-9519-4df2d558c3bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMapRingOfIntegersLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RingOfIntegersNormBound
namespace GlobalTheory.RingOfIntegersNormBound
theorem _root_.solution {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq, hqx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hqx
  have hlead : q.coeff q.natDegree = 1 := hq
  rw [hlead, map_one, one_mul] at hqx
  have hpow : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hqx
  have hpos : 0 < ‖x‖ := lt_trans one_pos hlt
  have key : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)
      rw [norm_mul, norm_pow]
      have h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)
      calc ‖algebraMap ℤ F (q.coeff n)‖ * ‖x‖ ^ n ≤ 1 * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖x‖ ^ n := one_mul _
        _ < _ := h1
  have := key q.natDegree
  rw [← norm_neg, ← hpow, norm_pow] at this
  exact lt_irrefl _ this
end GlobalTheory.RingOfIntegersNormBound
