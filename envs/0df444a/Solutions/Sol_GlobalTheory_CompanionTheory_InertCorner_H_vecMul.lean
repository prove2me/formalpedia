-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCorner.H_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:45:07.462794+00:00
-- url     : https://prove2.me/submissions/ecf07e82-bfe3-4488-8aa0-4ed30973a7a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_dv_vecMul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCorner
theorem _root_.solution (σ : L →+* L) (x y : Fin N → L) (A P Q : Matrix (Fin N) (Fin N) L) :
    H σ (x ᵥ* P) A (y ᵥ* Q) = H σ x (P * A * st σ Q) y := by
  unfold H
  rw [dv_vecMul, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.InertCorner
