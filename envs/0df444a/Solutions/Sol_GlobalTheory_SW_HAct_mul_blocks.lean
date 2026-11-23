-- Prove2me | solution 1 for GlobalTheory.SW.HAct.mul_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:07.650846+00:00
-- url     : https://prove2.me/submissions/9d4257a5-115a-49e0-96eb-2107a3230cb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution (τ : E →+* ℂ) (γ γ' : M2 E N) :
    (γ' * γ).toBlocks₁₁.map τ = γ'.toBlocks₁₁.map τ * γ.toBlocks₁₁.map τ +
        γ'.toBlocks₁₂.map τ * γ.toBlocks₂₁.map τ ∧
    (γ' * γ).toBlocks₁₂.map τ = γ'.toBlocks₁₁.map τ * γ.toBlocks₁₂.map τ +
        γ'.toBlocks₁₂.map τ * γ.toBlocks₂₂.map τ ∧
    (γ' * γ).toBlocks₂₁.map τ = γ'.toBlocks₂₁.map τ * γ.toBlocks₁₁.map τ +
        γ'.toBlocks₂₂.map τ * γ.toBlocks₂₁.map τ ∧
    (γ' * γ).toBlocks₂₂.map τ = γ'.toBlocks₂₁.map τ * γ.toBlocks₁₂.map τ +
        γ'.toBlocks₂₂.map τ * γ.toBlocks₂₂.map τ := by
  have h : (γ' * γ).map τ = γ'.map τ * γ.map τ := Matrix.map_mul
  rw [map_blocks, map_blocks τ γ, map_blocks τ γ', fromBlocks_multiply, fromBlocks_inj] at h
  exact h
end GlobalTheory.SW.HAct
