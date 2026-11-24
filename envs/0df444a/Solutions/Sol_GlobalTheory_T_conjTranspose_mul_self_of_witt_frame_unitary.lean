-- Prove2me | solution 1 for GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:33.438392+00:00
-- url     : https://prove2.me/submissions/0abfb3d2-beed-4f06-8952-afcec526f9d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConjStatement
import Theorems.Thm_GlobalTheory_conjTranspose_mul_mul_self_of_unitary_conj


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
theorem _root_.solution : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  first | exact @GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | exact GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | (intros; apply GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj <;> assumption)
end _root_.GlobalTheory.T
