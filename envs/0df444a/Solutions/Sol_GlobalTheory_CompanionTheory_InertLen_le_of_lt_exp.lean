-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.le_of_lt_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:15.478986+00:00
-- url     : https://prove2.me/submissions/eda2be6b-6990-4394-bb56-0569756b5795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertLen
theorem _root_.solution {x : WithZero (Multiplicative ℤ)} {k : ℕ} (h : x < WithZero.exp ((k + 1 : ℕ) : ℤ)) :
    x ≤ WithZero.exp (k : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨k', rfl⟩ : ∃ k' : ℤ, x = WithZero.exp k' := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    push_cast at h
    omega
end GlobalTheory.CompanionTheory.InertLen
