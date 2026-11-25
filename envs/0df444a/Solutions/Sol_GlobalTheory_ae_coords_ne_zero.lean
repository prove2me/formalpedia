-- Prove2me | solution 1 for GlobalTheory.ae_coords_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:21.20871+00:00
-- url     : https://prove2.me/submissions/1e931810-d98c-44df-b0cf-a0d56dec4c2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0
end GlobalTheory
