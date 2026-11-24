-- Prove2me | solution 1 for GlobalTheory.DiagonalKeyIdentity.diag_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:22:11.280095+00:00
-- url     : https://prove2.me/submissions/6fd6a351-c97c-4fc7-9cb2-fc29b3e3e02c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagKey

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalKeyIdentity
open Matrix
namespace GlobalTheory.DiagonalKeyIdentity
theorem _root_.solution {A : Type} [CommRing A] {q : ℕ} (a b : Fin q → A)
    (h : ∀ i, a i + b i + a i * b i = 0) :
    diagonal a + diagonal b + diagonal a * diagonal b = (0 : Matrix (Fin q) (Fin q) A) := by
  rw [diagonal_mul_diagonal, diagonal_add, diagonal_add, ← diagonal_zero]
  congr 1
  funext i
  exact h i
end GlobalTheory.DiagonalKeyIdentity
