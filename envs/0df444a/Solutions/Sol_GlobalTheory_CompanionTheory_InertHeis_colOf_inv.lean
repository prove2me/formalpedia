-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.colOf_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:07:13.311146+00:00
-- url     : https://prove2.me/submissions/5423dad2-ebf7-4996-af14-7668a63e1713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_colOf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_colOf_one

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
theorem _root_.solution {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : colOf u⁻¹ = -colOf u := by
  funext i
  have h := congrFun (colOf_mul hu (inv_mem hu)) i
  rw [mul_inv_cancel, colOf_one, Pi.zero_apply, Pi.add_apply] at h
  rw [Pi.neg_apply]
  linear_combination -h
end GlobalTheory.CompanionTheory.InertHeis
