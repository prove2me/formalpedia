-- Prove2me | solution 1 for GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:08.768592+00:00
-- url     : https://prove2.me/submissions/21afed1f-e7a0-4515-90f8-5bb1a74a4901

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeriesStatement
import Theorems.Thm_GlobalTheory_HeckeStrip_heckeSeries_eq_sum_pSeries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  first | exact @GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries | exact GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries | (intros; apply GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries <;> assumption)
end _root_.GlobalTheory.T
