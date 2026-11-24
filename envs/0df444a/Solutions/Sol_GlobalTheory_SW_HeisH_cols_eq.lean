-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.cols_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:12.727845+00:00
-- url     : https://prove2.me/submissions/936a9de5-6cdb-4ec1-8d6d-3b36927ec57b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_HAct_group_part


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution {γ : M2 E N} (hγ : γ ∈ UU E N) (d b : Matrix (Fin n) (Fin N) E) :
    d = (fromCols d b * γ⁻¹).toCols₁ * γ.toBlocks₁₁ + (fromCols d b * γ⁻¹).toCols₂ * γ.toBlocks₂₁ ∧
    b = (fromCols d b * γ⁻¹).toCols₁ * γ.toBlocks₁₂ + (fromCols d b * γ⁻¹).toCols₂ * γ.toBlocks₂₂ := by
  have h : fromCols d b * γ⁻¹ * γ = fromCols d b := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (HAct.group_part hγ).1, Matrix.mul_one]
  generalize fromCols d b * γ⁻¹ = X at h ⊢
  rw [← fromCols_toCols X, ← fromBlocks_toBlocks γ, fromCols_mul_fromBlocks] at h
  obtain ⟨h1, h2⟩ := fromCols_inj h
  exact ⟨h1.symm, h2.symm⟩
end GlobalTheory.SW.HeisH
