-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.mem_intL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:08.512541+00:00
-- url     : https://prove2.me/submissions/fa300a48-3fdb-4e1b-b485-26bba08af721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_AdditiveVectorExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl
end GlobalTheory.CompanionTheory.InertZeta
