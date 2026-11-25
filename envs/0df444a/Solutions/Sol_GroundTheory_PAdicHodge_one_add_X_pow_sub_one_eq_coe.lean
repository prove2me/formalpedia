-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_add_X_pow_sub_one_eq_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:23:17.36205+00:00
-- url     : https://prove2.me/submissions/209b44a5-bcf4-4e33-928c-2a7075181883

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution (q : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ q - 1) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1 : Polynomial ℚ) : ℚ⟦X⟧) := by
  simp
end GroundTheory.PAdicHodge
