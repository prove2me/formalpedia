-- Prove2me | solution 1 for GlobalTheory.NatMulIntegral.exists_nat_mul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:51.976065+00:00
-- url     : https://prove2.me/submissions/22de5a8c-460d-4ce2-87a3-a622611b5124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNatSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulIntegral
open NumberField
namespace GlobalTheory.NatMulIntegral
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]
    exact hi
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h', Int.cast_neg, neg_mul]
    exact hi.neg
end GlobalTheory.NatMulIntegral
