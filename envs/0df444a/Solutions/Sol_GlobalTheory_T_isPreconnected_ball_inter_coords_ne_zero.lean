-- Prove2me | solution 1 for GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:23:24.715033+00:00
-- url     : https://prove2.me/submissions/47a3513b-9541-4eaf-a913-7aa2ac3a1715

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZeroStatement
import Theorems.Thm_GlobalTheory_isPreconnected_polydisc_first_coords_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  first | exact @GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | exact GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | (intros; apply GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero <;> assumption)
end _root_.GlobalTheory.T
