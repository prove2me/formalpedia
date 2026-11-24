-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.colOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:11:45.840788+00:00
-- url     : https://prove2.me/submissions/10619c3b-243a-4a79-8890-387260816dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution : colOf (1 : GU σ (N + 2)) = 0 := by
  funext i
  show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (Fin.last (N + 1)) = 0
  exact Matrix.one_apply_ne (mid_ne_last i)
end GlobalTheory.CompanionTheory.InertHeis
