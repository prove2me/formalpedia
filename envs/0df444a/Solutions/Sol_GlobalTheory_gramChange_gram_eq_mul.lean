-- Prove2me | solution 1 for GlobalTheory.gramChange_gram_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:01.375944+00:00
-- url     : https://prove2.me/submissions/39e86d05-4f07-4c69-861a-6c14c0a9af7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} [Fintype ι]
    (u : ι → Fin n → K) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k) = (Matrix.of u).map σ * (Matrix.of u)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]
end GlobalTheory
