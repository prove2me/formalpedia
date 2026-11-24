-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.edge_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:54:00.462889+00:00
-- url     : https://prove2.me/submissions/9e606987-4259-4341-89d8-39fd0d20b6a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertLevi
theorem _root_.solution (c d : L) (f : Fin N → L) : edge c d f (Fin.last (N + 1)) = d := by
  rw [edge, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
end GlobalTheory.CompanionTheory.InertLevi
