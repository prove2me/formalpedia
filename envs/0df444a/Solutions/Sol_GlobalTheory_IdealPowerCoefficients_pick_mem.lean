-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.pick_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:16.019219+00:00
-- url     : https://prove2.me/submissions/3df3aa80-9e58-4ed8-ba7d-cffce830007b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}
namespace GlobalTheory.IdealPowerCoefficients
theorem _root_.solution (d : κ →₀ ℕ) (h : d ≠ 0) (k : κ) : pick d k ∈ d.support := by
  have h' : d.support.Nonempty := Finsupp.support_nonempty_iff.2 h
  rw [pick, dif_pos h']
  exact h'.choose_spec
end GlobalTheory.IdealPowerCoefficients
