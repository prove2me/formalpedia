-- Prove2me | solution 1 for GlobalTheory.InertZeta.cornerOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:12.72625+00:00
-- url     : https://prove2.me/submissions/b8be0792-251f-48d1-a5a7-1c9e22926b4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero


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
theorem _root_.solution : cornerOf (1 : GU σ (N + 2)) = 0 :=
  Matrix.one_apply_ne (last_ne_zero (N := N)).symm
end GlobalTheory.InertZeta
