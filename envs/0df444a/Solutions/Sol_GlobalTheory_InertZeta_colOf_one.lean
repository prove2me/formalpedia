-- Prove2me | solution 1 for GlobalTheory.InertZeta.colOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:47:58.717661+00:00
-- url     : https://prove2.me/submissions/9c09c868-bcd8-4505-9997-801c9cc949ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
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
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.InertZeta
theorem _root_.solution : colOf (1 : GU σ (N + 2)) = 0 := funext fun i =>
  Matrix.one_apply_ne (mid_ne_last i)
end GlobalTheory.InertZeta
