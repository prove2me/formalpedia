-- Prove2me | solution 1 for GlobalTheory.T.plucker_minors_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:24.433706+00:00
-- url     : https://prove2.me/submissions/6d7a9a0c-8da5-4049-85d8-4669c5942845

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportionalStatement
import Theorems.Thm_GlobalTheory_jacobi_complementary_minors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] {p q : ℕ} (α : Matrix (Fin p) (Fin p ⊕ Fin q) K) (β : Matrix (Fin q) (Fin p ⊕ Fin q) K),
  α * β.transpose = 0 →
  (∃ π₀ : Equiv.Perm (Fin p ⊕ Fin q), (α.submatrix id (π₀ ∘ Sum.inl)).det ≠ 0) →
  (∃ π₁ : Equiv.Perm (Fin p ⊕ Fin q), (β.submatrix id (π₁ ∘ Sum.inr)).det ≠ 0) →
  ∃ lam : K, ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
    ((Equiv.Perm.sign π : ℤ) : K) * (α.submatrix id (π ∘ Sum.inl)).det = lam * (β.submatrix id (π ∘ Sum.inr)).det := by
  first | exact @GlobalTheory.jacobi_complementary_minors | exact GlobalTheory.jacobi_complementary_minors | (intros; apply GlobalTheory.jacobi_complementary_minors <;> assumption)
end _root_.GlobalTheory.T
