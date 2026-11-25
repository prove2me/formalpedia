-- Prove2me | solution 1 for GlobalTheory.T.gaussSum_nondegenerate_finite_hermitian_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:21:18.781865+00:00
-- url     : https://prove2.me/submissions/b7312535-f7c3-44dd-ade3-44e419bffb48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModuleStatement
import Theorems.Thm_GlobalTheory_HermitianGauss_gauss_hermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FinWeil
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  first | exact @GlobalTheory.HermitianGauss.gauss_hermitian | exact GlobalTheory.HermitianGauss.gauss_hermitian | (intros; apply GlobalTheory.HermitianGauss.gauss_hermitian <;> assumption)
end _root_.GlobalTheory.T
