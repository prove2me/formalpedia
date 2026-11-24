-- Prove2me | solution 1 for GlobalTheory.IntegralMultipleClearDenominators.exists_nat_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:51:46.904822+00:00
-- url     : https://prove2.me/submissions/945bc08a-e4f0-436a-a6fd-5c9ce0ef07d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultipleClearDenominators
open NumberField
namespace GlobalTheory.IntegralMultipleClearDenominators
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h1 | h1
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h1]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h1]
      rw [Int.cast_neg, neg_neg]
      exact (Int.cast_natCast _).symm
    rw [this, neg_mul]; exact hint.neg
end GlobalTheory.IntegralMultipleClearDenominators
