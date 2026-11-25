-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.digitSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:31.325638+00:00
-- url     : https://prove2.me/submissions/381a0c39-2ad7-492e-85a4-b224e20d3248

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreBounds
theorem _root_.solution (l N : ℕ) (hl : 1 < l) :
    (Nat.digits l N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hlen : (Nat.digits l N).length = Nat.log l N + 1 := Nat.length_digits l N hl hN.ne'
    have hd : ∀ d ∈ Nat.digits l N, d ≤ l - 1 := fun d hd => by
      have := Nat.digits_lt_base hl hd
      omega
    calc (Nat.digits l N).sum ≤ (Nat.digits l N).length * (l - 1) := by
          simpa [smul_eq_mul] using List.sum_le_card_nsmul _ _ hd
      _ = (Nat.log l N + 1) * (l - 1) := by rw [hlen]
end GlobalTheory.LegendreBounds
