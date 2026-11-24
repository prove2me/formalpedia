-- Prove2me | solution 1 for GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:10:06.043073+00:00
-- url     : https://prove2.me/submissions/c92f0fe4-dbb6-4bed-9378-d9c024a86b0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsCutoffOfAddCharTranslationInvariantFunctio
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsIntegralScaledBoxPiSupersetOfIsCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralBoxInvariantEqMeasureRealMulSumRepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsCutoffOfAddCharTranslationInvariantFunctioStatement
import Theorems.Thm_GlobalTheory_CharCutoff_exists_cutoff_of_char_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  first | exact @GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant | exact GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant | (intros; apply GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant <;> assumption)
end _root_.GlobalTheory.T
