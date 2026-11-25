-- Prove2me | solution 1 for GlobalTheory.Doubling.npow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:43:57.841172+00:00
-- url     : https://prove2.me/submissions/25831fab-2afd-4184-bb99-831b0fc70689

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_norm_npow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
namespace GlobalTheory.Doubling
theorem _root_.solution {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_npow hr]; exact (Real.rpow_pos_of_pos hr _).ne'
end GlobalTheory.Doubling
