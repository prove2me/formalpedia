-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.cornerOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:24.110907+00:00
-- url     : https://prove2.me/submissions/d20a3324-6dbd-4a9c-b8e0-dccdf1003ed7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution : cornerOf (1 : GU σ (N + 2)) = 0 := by
  show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 (Fin.last (N + 1)) = 0
  exact Matrix.one_apply_ne (fun h => last_ne_zero h.symm)
end GlobalTheory.CompanionTheory.InertHeis
