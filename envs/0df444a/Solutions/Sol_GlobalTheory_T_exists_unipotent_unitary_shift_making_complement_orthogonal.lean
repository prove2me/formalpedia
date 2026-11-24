-- Prove2me | solution 1 for GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:28.142854+00:00
-- url     : https://prove2.me/submissions/6597e715-fb56-4ce1-bbf6-d37b584492e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplexStatement
import Theorems.Thm_GlobalTheory_levi_element_cpx


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
theorem _root_.solution : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  first | exact @GlobalTheory.levi_element_cpx | exact GlobalTheory.levi_element_cpx | (intros; apply GlobalTheory.levi_element_cpx <;> assumption)
end _root_.GlobalTheory.T
