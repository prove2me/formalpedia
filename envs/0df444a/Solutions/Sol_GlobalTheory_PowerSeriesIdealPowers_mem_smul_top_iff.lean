-- Prove2me | solution 1 for GlobalTheory.PowerSeriesIdealPowers.mem_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:28.042808+00:00
-- url     : https://prove2.me/submissions/a003cc7e-6bad-4116-9536-571abe484ac8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.PowerSeriesIdealPowers
theorem _root_.solution {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]
end GlobalTheory.PowerSeriesIdealPowers
