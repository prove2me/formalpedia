-- Prove2me | solution 1 for GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:31.018857+00:00
-- url     : https://prove2.me/submissions/e174514f-f096-4a94-bb22-3573fa439a41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealMembership
namespace GlobalTheory.MaximalIdealMembership
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (f : MvPowerSeries (Fin a) O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ↔
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
end GlobalTheory.MaximalIdealMembership
