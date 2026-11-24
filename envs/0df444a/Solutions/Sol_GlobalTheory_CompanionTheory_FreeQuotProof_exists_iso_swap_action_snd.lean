-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:35.689129+00:00
-- url     : https://prove2.me/submissions/310da46d-0c60-4311-a75a-a92493a3b9f4

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ShearIsoActionProjection
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_action_eq_fst_smul_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof
namespace GlobalTheory.CompanionTheory.FreeQuotProof
theorem _root_.solution : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  intro S G X _ _
  have hγ : (γ[G, X] : G ⊗ X ⟶ X) = fst G X • snd G X := GlobalTheory.CompanionTheory.FreeQuotProof.action_eq_fst_smul_snd G X
  obtain ⟨σ, h₁, h₂⟩ : ∃ σ : G ⊗ X ⟶ G ⊗ X,
      σ ≫ snd G X = fst G X • snd G X ∧ σ ≫ fst G X = (fst G X)⁻¹ :=
    ⟨lift (fst G X)⁻¹ (fst G X • snd G X), lift_snd _ _, lift_fst _ _⟩
  have h₃ : σ ≫ (fst G X • snd G X) = snd G X := by
    rw [CategoryTheory.ModObj.comp_smul, h₂, h₁, inv_smul_smul]
  have h₄ : σ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, h₂, CategoryTheory.Hom.inv_def, ← Category.assoc, h₂,
        ← CategoryTheory.Hom.inv_def, inv_inv, Category.id_comp]
    · rw [Category.assoc, h₁, h₃, Category.id_comp]
  exact ⟨σ, ⟨σ, h₄, h₄⟩, by rw [hγ]; exact h₁, by rw [hγ]; exact h₃⟩
end GlobalTheory.CompanionTheory.FreeQuotProof
