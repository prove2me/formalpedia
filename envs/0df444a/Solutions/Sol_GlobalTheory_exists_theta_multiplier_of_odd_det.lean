-- Prove2me | solution 1 for GlobalTheory.exists_theta_multiplier_of_odd_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:03:07.856915+00:00
-- url     : https://prove2.me/submissions/0e204940-724f-4a64-9ef3-576a7269387a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_IsSiegel_exists_riemannTheta_multiplier
import Theorems.Thm_GlobalTheory_isHoloSiegel_of_theta_transform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hodd : Odd γ.toBlocks₂₂.det)
    (hb : ∀ μ, Even (μ ⬝ᵥ (γ.toBlocks₂₂ᵀ * γ.toBlocks₁₂) *ᵥ μ))
    (hc : ∀ μ, Even (μ ⬝ᵥ (γ.toBlocks₁₁ᵀ * γ.toBlocks₂₁) *ᵥ μ)) :
    ∃ l : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g l ∧ ∀ τ ∈ SiegelH (Fin g),
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ) ∧
      l τ ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det := by
  have H (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g)) : ∃ l : ℂ,
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l * theta 0 0 z τ) ∧
      l ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det := by
    obtain ⟨l, h1, h2⟩ := IsSiegel.exists_riemannTheta_multiplier ⟨hτ.1, hτ.2⟩
      (by rwa [fromBlocks_toBlocks]) hodd hb hc
    refine ⟨l, fun z => ?_, h1⟩
    rw [eC, show 2 * π * I * (-expArg γ τ z / 2) = -(π * I) * expArg γ τ z by ring]
    exact h2 z
  choose! l hl using H
  exact ⟨l, isHoloSiegel_of_theta_transform hγ fun τ hτ => (hl τ hτ).1, hl⟩
end GlobalTheory
