-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.row_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:58:54.825899+00:00
-- url     : https://prove2.me/submissions/f745782e-e034-4b88-82f6-a367354cea0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rowOf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rowOf_one
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rowOf_inv

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
theorem _root_.solution {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) (j : Fin N) : rowOf u j = -σ (colOf u j.rev) := by
  have h := congrFun (rowOf_mul hu (inv_mem hu)) j
  rw [mul_inv_cancel, rowOf_one, Pi.zero_apply, Pi.add_apply, rowOf_inv] at h
  linear_combination -h
end GlobalTheory.CompanionTheory.InertHeis
