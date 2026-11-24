-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertIndex.mem_intL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:56.224828+00:00
-- url     : https://prove2.me/submissions/28bb8ea9-512e-4cc7-8a4e-d28b4bc58ccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LatticeIndexOfSmith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertIndex
theorem _root_.solution {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl
end GlobalTheory.CompanionTheory.InertIndex
