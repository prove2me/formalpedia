-- Prove2me | solution 1 for GlobalTheory.InertZeta.HeisCoord.last_ne_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:52.63508+00:00
-- url     : https://prove2.me/submissions/99289041-9276-4faf-8c66-ff43eb48fb43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last


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
theorem _root_.solution (i : Fin N) : Fin.last (N + 1) ≠ mid i := (mid_ne_last i).symm
end GlobalTheory.InertZeta.HeisCoord
