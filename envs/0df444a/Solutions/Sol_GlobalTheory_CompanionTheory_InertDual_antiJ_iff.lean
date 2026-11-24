-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDual.antiJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:11.873547+00:00
-- url     : https://prove2.me/submissions/97ace3c5-6768-43c4-b684-4735aea73fb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDual
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertDual
theorem _root_.solution (i j : Fin N) : i.val + j.val + 1 = N ↔ j = i.rev := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.isLt
  have := j.isLt
  constructor <;> intro h <;> omega
end GlobalTheory.CompanionTheory.InertDual
