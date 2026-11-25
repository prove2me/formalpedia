-- Prove2me | solution 1 for GlobalTheory.T.tensor_prime_over_ideal_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:08.104552+00:00
-- url     : https://prove2.me/submissions/4787ba63-2c1d-4ca6-8804-57a9fc501b29

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeOverIdealCompletion
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeOverIdealCompletionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KrullBaseChange_krull_after_base_change


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M), (∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈ LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C)) → ∀ Q₁ : Ideal (R ⊗[B] C), Q₁.IsPrime → I.map (algebraMap B R) ≤ Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) → ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | exact GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | (intros; apply GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change <;> assumption)
end _root_.GlobalTheory.T
