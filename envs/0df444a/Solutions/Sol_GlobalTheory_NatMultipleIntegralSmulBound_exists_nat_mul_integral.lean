-- Prove2me | solution 1 for GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:35.384814+00:00
-- url     : https://prove2.me/submissions/4c0a018b-1a8a-411d-bb19-6485b405b179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatSmulLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMultipleIntegralSmulBound
open NumberField
namespace GlobalTheory.NatMultipleIntegralSmulBound
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : RingOfIntegers E, (b : E) = (m : E) * a := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy),
    ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩
  show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a
  rw [smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]
end GlobalTheory.NatMultipleIntegralSmulBound
