-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.corner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:28:27.500956+00:00
-- url     : https://prove2.me/submissions/8f1b4834-c91d-480f-9bc9-af3fde312e72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_cornerOf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_cornerOf_one
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_cornerOf_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_colOf_inv

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
theorem _root_.solution {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u := by
  have h := cornerOf_mul hu (inv_mem hu)
  rw [mul_inv_cancel, cornerOf_one, cornerOf_inv, colOf_inv hu, dotProduct_neg] at h
  linear_combination -h
end GlobalTheory.CompanionTheory.InertHeis
