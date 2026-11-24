-- Prove2me | solution 1 for GlobalTheory.TwoVarValRing.not_X_one_dvd_X_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:28.379163+00:00
-- url     : https://prove2.me/submissions/54e168e3-ec98-4641-9247-6caedeb8902f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwoVarValRing
namespace GlobalTheory.TwoVarValRing
theorem _root_.solution (k : Type) [Field k] :
    ¬ MvPowerSeries.X 1 ∣ (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro h
  have := h (Finsupp.single 0 1) (by simp)
  simp [MvPowerSeries.coeff_index_single_self_X] at this
end GlobalTheory.TwoVarValRing
