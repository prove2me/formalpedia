-- Prove2me | solution 1 for GlobalTheory.T.hermitian_flag_complement_posDef_factorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:57.573574+00:00
-- url     : https://prove2.me/submissions/51d35bf5-2057-4e23-bbb5-7667515b993c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagComplementPosDefFactorization
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagComplementPosDefFactorizationStatement
import Theorems.Thm_GlobalTheory_schur_complement_step_cpx


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
theorem _root_.solution : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  first | exact @GlobalTheory.schur_complement_step_cpx | exact GlobalTheory.schur_complement_step_cpx | (intros; apply GlobalTheory.schur_complement_step_cpx <;> assumption)
end _root_.GlobalTheory.T
