-- Prove2me | solution 1 for GlobalTheory.exists_lt_norm_lt_one_of_densely
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:02.946551+00:00
-- url     : https://prove2.me/submissions/ba23a6cd-1ca7-4b9a-9414-17f3a147cba8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology MvPowerSeries
namespace GlobalTheory
theorem _root_.solution {C : Type*} [DenselyNormedField C] (r : ℝ) (hr : r < 1) :
    ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1 := by
  obtain ⟨x, h1, h2⟩ := NormedField.exists_lt_norm_lt C (le_max_right r 0) (max_lt hr one_pos)
  exact ⟨x, (le_max_left r 0).trans_lt h1, h2⟩
end GlobalTheory
