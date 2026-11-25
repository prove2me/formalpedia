-- Prove2me | solution 1 for GlobalTheory.UnitNormPowerSubOne.norm_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:47.530574+00:00
-- url     : https://prove2.me/submissions/8d582baf-6e87-4a39-a96f-1ab0c2d9f779

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Theorems.Thm_GlobalTheory_UnitNormPowerSubOne_norm_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitNormPowerSubOne
namespace GlobalTheory.UnitNormPowerSubOne
theorem _root_.solution {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := IsUltrametricDist.norm_add_le_max (u ^ n * (u - 1)) (u ^ n - 1)
    have e : u ^ n * (u - 1) + (u ^ n - 1) = u ^ (n + 1) - 1 := by ring
    rw [e, norm_mul, norm_pow, norm_eq_one u h, one_pow, one_mul] at h1
    exact h1.trans (max_le le_rfl ih)
end GlobalTheory.UnitNormPowerSubOne
