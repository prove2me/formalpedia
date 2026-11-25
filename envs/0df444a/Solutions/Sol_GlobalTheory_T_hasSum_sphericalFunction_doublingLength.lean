-- Prove2me | solution 1 for GlobalTheory.T.hasSum_sphericalFunction_doublingLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:41.342981+00:00
-- url     : https://prove2.me/submissions/03374ece-663d-4ac7-bb42-e1b0f69d0e93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLengthStatement
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_doublingLength


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  first | exact @GlobalTheory.DoublingLength.hasSum_doublingLength | exact GlobalTheory.DoublingLength.hasSum_doublingLength | (intros; apply GlobalTheory.DoublingLength.hasSum_doublingLength <;> assumption)
end _root_.GlobalTheory.T
