-- Prove2me | solution 1 for GlobalTheory.T.unitary_act_halfSpace_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:58:01.543422+00:00
-- url     : https://prove2.me/submissions/9e180a48-0958-4067-ade0-ce38f585d278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (N : ℕ) (γ : M2 E N), γ ∈ UU E N → (IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧ γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) ∧ ∀ γ' ∈ UU E N, γ' * γ ∈ UU E N) ∧ ∀ Z ∈ Hn Ψ N, (∀ τ, (hDen Ψ γ Z τ).det ≠ 0 ∧ (hDen' Ψ γ Z τ).det * τ.1 γ.det = (hDen Ψ γ Z τ).det ∧ ‖τ.1 γ.det‖ = 1 ∧ (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ)) ∧ hAct Ψ γ Z ∈ Hn Ψ N ∧ detIm (hAct Ψ γ Z) * ∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2 = detIm Z ∧ ∀ γ' ∈ UU E N, hAct Ψ (γ' * γ) Z = hAct Ψ γ' (hAct Ψ γ Z) ∧ (∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ) ∧ ∀ τ, hDen' Ψ (γ' * γ) Z τ = hDen' Ψ γ Z τ * hDen' Ψ γ' (hAct Ψ γ Z) τ := by
  first | exact @GlobalTheory.SW.unitary_act_halfSpace | exact GlobalTheory.SW.unitary_act_halfSpace | (intros; apply GlobalTheory.SW.unitary_act_halfSpace <;> assumption)
end _root_.GlobalTheory.T
