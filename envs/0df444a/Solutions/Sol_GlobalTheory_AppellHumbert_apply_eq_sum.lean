-- Prove2me | solution 1 for GlobalTheory.AppellHumbert.apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:08.277789+00:00
-- url     : https://prove2.me/submissions/783045e2-f85a-4381-b961-0efbde41e8f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertNormalFormOfLinearExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AppellHumbert
namespace GlobalTheory.AppellHumbert
theorem _root_.solution {g : ℕ} (φ : (Fin g → ℂ) →ₗ[ℂ] ℂ) (z : Fin g → ℂ) :
    φ z = ∑ i, z i * φ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' z]
  simp [map_sum]
end GlobalTheory.AppellHumbert
