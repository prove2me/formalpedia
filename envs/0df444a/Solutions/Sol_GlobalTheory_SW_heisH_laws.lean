-- Prove2me | solution 1 for GlobalTheory.SW.heisH_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:32.652668+00:00
-- url     : https://prove2.me/submissions/a424991d-8905-4826-ad50-de6f0d4a17d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_HeisH_isSB_heisH
import Theorems.Thm_GlobalTheory_SW_HeisH_thH_heisH
import Theorems.Thm_GlobalTheory_SW_HeisH_cols_eq
import Theorems.Thm_GlobalTheory_SW_HeisH_transH_heisH
import Theorems.Thm_GlobalTheory_T_hermitianWeilAction_unitaryGroup_testFunctions


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
open GlobalTheory.SW.HeisH
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsSB (heisH d b φ) ∧ (∀ Z ∈ Hn Ψ N, ∀ z z' : CM Ψ n N, thH Ψ (heisH d b φ) Z z z' = cexp (2 * π * I * expo Ψ d Z z z' + π * I * ((Algebra.trace ℚ E (∑ k, ∑ a, b k a * cc (d k a)) : ℚ) : ℂ)) * thH Ψ φ Z (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ)) ∧ ∀ γ ∈ UU E N, weil Ψ γ (heisH d b φ) = heisH (Matrix.fromCols d b * γ⁻¹).toCols₁ (Matrix.fromCols d b * γ⁻¹).toCols₂ (weil Ψ γ φ) := by
  intro E _ _ _ Ψ hΨ n N hn d b φ hφ
  refine ⟨isSB_heisH d b hφ, fun Z _ z z' => thH_heisH hΨ d b φ Z z z', fun γ hγ => ?_⟩
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ φ hφ
  have h3 := transH_heisH hΨ hγ (fromCols d b * γ⁻¹).toCols₁ (fromCols d b * γ⁻¹).toCols₂ h2
  rw [← (cols_eq hγ d b).1, ← (cols_eq hγ d b).2] at h3
  exact ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (isSB_heisH d b hφ)).2.2.1 _ (isSB_heisH _ _ h1) h3).symm
end GlobalTheory.SW
