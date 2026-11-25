-- Prove2me | solution 1 for GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:03.868+00:00
-- url     : https://prove2.me/submissions/b9a7fbd7-35fa-4f37-9891-2af826fe41ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Theorems.Thm_GlobalTheory_SW_exists_symplectic_of_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by
  first | exact @GlobalTheory.SW.exists_symplectic_of_unitary | exact GlobalTheory.SW.exists_symplectic_of_unitary | (intros; apply GlobalTheory.SW.exists_symplectic_of_unitary <;> assumption)
end _root_.GlobalTheory.T
