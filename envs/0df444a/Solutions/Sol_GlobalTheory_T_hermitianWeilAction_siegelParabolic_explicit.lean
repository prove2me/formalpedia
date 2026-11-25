-- Prove2me | solution 1 for GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:00.816262+00:00
-- url     : https://prove2.me/submissions/3aadfe81-05ce-4737-8d6f-2db9112db2d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Theorems.Thm_GlobalTheory_SW_weil_parabolic


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → (∀ γ ∈ UU E N, γ.toBlocks₂₁ = 0 → ∀ x, weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * chiH Ψ (-(γ.toBlocks₁₂ * ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ UU E N, ∀ γ' ∈ UU E N, botSpan γ = botSpan γ' → ∀ Z ∈ Hn Ψ N, ∀ z z', eisTerm Ψ γ φ Z z z' = eisTerm Ψ γ' φ Z z z' := by
  first | exact @GlobalTheory.SW.weil_parabolic | exact GlobalTheory.SW.weil_parabolic | (intros; apply GlobalTheory.SW.weil_parabolic <;> assumption)
end _root_.GlobalTheory.T
