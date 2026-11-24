-- Prove2me | solution 1 for GlobalTheory.ConjugateAlgebraLemmas.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:02.718999+00:00
-- url     : https://prove2.me/submissions/a71e275d-9805-44c5-8a5f-d5982c2d118e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateAlgebraLemmas
open Matrix
namespace GlobalTheory.ConjugateAlgebraLemmas
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) (a b : Fin n → K) :
    ∑ k : Fin n, σ ((g *ᵥ a) k) * (g *ᵥ b) k = ∑ k : Fin n, σ (a k) * b k := by
  have h1 : ∀ k, σ ((g *ᵥ a) k) = ((g.map σ) *ᵥ (fun i => σ (a i))) k := by
    intro k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp_rw [h1]
  change (g.map σ *ᵥ fun i => σ (a i)) ⬝ᵥ (g *ᵥ b) = (fun i => σ (a i)) ⬝ᵥ b
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hg, Matrix.vecMul_one]
end GlobalTheory.ConjugateAlgebraLemmas
