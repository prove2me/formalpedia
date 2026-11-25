-- Prove2me | solution 1 for GlobalTheory.UnitNormPowerSubOne.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:30.410961+00:00
-- url     : https://prove2.me/submissions/5cef54ed-7724-4833-a329-eeccc365ba07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe

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
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    have e : u + -(u - 1) = 1 := by ring
    rw [e, norm_one, norm_neg] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)
end GlobalTheory.UnitNormPowerSubOne
