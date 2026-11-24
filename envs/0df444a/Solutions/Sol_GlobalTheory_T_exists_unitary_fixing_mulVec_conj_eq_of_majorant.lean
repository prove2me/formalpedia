-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:08.252289+00:00
-- url     : https://prove2.me/submissions/e41c5c8b-4d6a-430c-8187-272047ea91da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorantStatement
import Theorems.Thm_GlobalTheory_radical_elt_moving_dual_to_majorant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → θ * θ = 1 → (J * θ).PosDef →
    ∀ (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ), X₂.conjTranspose * J * X₂ = 0 → Y₂.conjTranspose * J * Y₂ = 0 →
      X₂.conjTranspose * J * Y₂ = 1 →
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 → ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  first | exact @GlobalTheory.radical_elt_moving_dual_to_majorant | exact GlobalTheory.radical_elt_moving_dual_to_majorant | (intros; apply GlobalTheory.radical_elt_moving_dual_to_majorant <;> assumption)
end _root_.GlobalTheory.T
