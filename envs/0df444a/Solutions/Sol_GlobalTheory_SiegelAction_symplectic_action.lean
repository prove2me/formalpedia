-- Prove2me | solution 1 for GlobalTheory.SiegelAction.symplectic_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:16:10.939431+00:00
-- url     : https://prove2.me/submissions/10d7a4b6-7efe-407d-90a1-97c140b8e394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Theorems.Thm_GlobalTheory_SiegelAction_act_complex
import Theorems.Thm_GlobalTheory_SiegelAction_qm_conj
import Theorems.Thm_GlobalTheory_SiegelAction_qm_add
import Theorems.Thm_GlobalTheory_SiegelAction_qm_mul
import Theorems.Thm_GlobalTheory_SiegelAction_qm_blocks_mem
import Theorems.Thm_GlobalTheory_SiegelAction_toBlocks_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι,
    (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧
    (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj =
      τ.map (fun z => (z.im : ℂ)) ∧
    ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧
      spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  intro ι _ _ σ hσ τ hτ
  obtain ⟨h1, h2, h3, h4⟩ := act_complex (qm_blocks_mem hσ) (qm_conj _) (qm_conj _) (qm_conj _)
    (qm_conj _) hτ
  refine ⟨h1, h2, h3, h4, fun σ' _ => ?_⟩
  have hu : IsUnit (spDen σ τ).det := h1.isUnit
  have hWQ : spAct σ τ * spDen σ τ = qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ :=
    nonsing_inv_mul_cancel_right _ _ hu
  obtain ⟨m1, m2, m3, m4⟩ := toBlocks_mul σ' σ
  have gen : ∀ X Y : Matrix ι ι ℚ,
      qm (X * σ.toBlocks₁₁ + Y * σ.toBlocks₂₁) * τ + qm (X * σ.toBlocks₁₂ + Y * σ.toBlocks₂₂) =
        (qm X * spAct σ τ + qm Y) * spDen σ τ := by
    intro X Y
    rw [Matrix.add_mul (qm X * spAct σ τ), Matrix.mul_assoc, hWQ]
    simp only [qm_add, qm_mul, spDen]
    noncomm_ring
  have hden : spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ := by
    rw [spDen, m3, m4, gen]; rfl
  refine ⟨hden, ?_⟩
  rw [spAct, hden, m1, m2, gen, Matrix.mul_inv_rev, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]
  rfl
end GlobalTheory.SiegelAction
