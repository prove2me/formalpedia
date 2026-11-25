-- Prove2me | solution 1 for GroundTheory.PAdicHodge.X_dvd_one_add_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:20.662186+00:00
-- url     : https://prove2.me/submissions/26c22225-97d7-48ee-96e0-066a80d84ee1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution {R : Type*} [CommRing R] (q : ℕ) :
    (Polynomial.X : Polynomial R) ∣ (1 + Polynomial.X) ^ q - 1 := by
  have h := sub_dvd_pow_sub_pow (1 + Polynomial.X : Polynomial R) 1 q
  rwa [one_pow, add_sub_cancel_left] at h
end GroundTheory.PAdicHodge
