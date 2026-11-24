-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.isFirst_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:35.398403+00:00
-- url     : https://prove2.me/submissions/dbcfe5ad-d0a4-418c-a872-97f8f4b3672a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {a : ℕ} {m : Fin a →₀ ℕ} {i j : Fin a} (hi : IsFirst m i)
    (hj : IsFirst m j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (hj.2 i h) hi.1
  · exact h
  · exact absurd (hi.2 j h) hj.1
end GlobalTheory.FiltrationMultiplicative
