-- Prove2me | solution 1 for GlobalTheory.InertZeta.det_mat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:48:00.949946+00:00
-- url     : https://prove2.me/submissions/fe5a795c-9033-4971-ba7b-cfb497a91d44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.InertZeta
theorem _root_.solution {n : ℕ} (g : GU σ n) : (mat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n) L).isUnit).ne_zero
end GlobalTheory.InertZeta
