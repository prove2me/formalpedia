-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.pick_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:15.377731+00:00
-- url     : https://prove2.me/submissions/a5e64042-ad43-45dc-9d56-6b775afc1cbf

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
theorem _root_.solution (d : κ →₀ ℕ) (h : d ≠ 0) (k k' : κ) : pick d k = pick d k' := by
  have h' : d.support.Nonempty := Finsupp.support_nonempty_iff.2 h
  simp [pick, h']
end GlobalTheory.IdealPowerCoefficients
