-- Prove2me | solution 1 for GlobalTheory.InertZeta.HeisCoord.zero_ne_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:14.862269+00:00
-- url     : https://prove2.me/submissions/2206967e-5066-48ec-9426-028d726a8a14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.HeisCoord
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta.HeisCoord
theorem _root_.solution (i : Fin N) : (0 : Fin (N + 2)) ≠ mid i := (mid_ne_zero i).symm
end GlobalTheory.InertZeta.HeisCoord
