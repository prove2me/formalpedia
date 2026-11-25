-- Prove2me | solution 1 for GlobalTheory.Phase.ParabValues.values_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:19.953943+00:00
-- url     : https://prove2.me/submissions/0116795c-f31b-4315-a481-6f584210ca92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase
import Theorems.Thm_GlobalTheory_Phase_ParabValues_ph_rat_mul_exp
import Theorems.Thm_GlobalTheory_Phase_ParabValues_trans_explicit
import Theorems.Thm_GlobalTheory_Phase_ParabValues_trans_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ParabValues
open GlobalTheory.SW.Parab
namespace GlobalTheory.Phase.ParabValues
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  intro κ ι _ _ _ _ σ hσ hC φ ψ hφ hψ h y
  obtain ⟨h1, h2⟩ := trans_explicit κ ι σ hσ hC φ hφ
  have e := trans_unique κ ι σ hσ φ _ _ hψ h1 h h2
  refine ⟨((σ.toBlocks₂₂.det ^ (Fintype.card κ / 2) : ℚ) : ℂ) *
    parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) y, y * σ.toBlocks₁₁, ph_rat_mul_exp _ _, ?_⟩
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
end GlobalTheory.Phase.ParabValues
