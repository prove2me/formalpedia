-- Prove2me | solution 1 for GlobalTheory.CloseToUnitNorm.norm_eq_one_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:28.358799+00:00
-- url     : https://prove2.me/submissions/6d349f82-fbf0-4f24-91b0-977a7a72e4c6

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
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (1 - u)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)
end GlobalTheory.CloseToUnitNorm
