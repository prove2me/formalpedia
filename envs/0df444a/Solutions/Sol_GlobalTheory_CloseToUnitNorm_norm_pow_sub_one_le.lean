-- Prove2me | solution 1 for GlobalTheory.CloseToUnitNorm.norm_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:29.178277+00:00
-- url     : https://prove2.me/submissions/95f3846a-6348-49e5-bbc3-36b2c8ba33d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CloseToUnitNorm
namespace GlobalTheory.CloseToUnitNorm
theorem _root_.solution {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hu, one_mul]
    exact ih
end GlobalTheory.CloseToUnitNorm
