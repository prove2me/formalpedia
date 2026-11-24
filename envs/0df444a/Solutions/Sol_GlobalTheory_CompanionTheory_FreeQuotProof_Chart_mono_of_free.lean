-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.mono_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:35:57.07286+00:00
-- url     : https://prove2.me/submissions/b0b5b019-bca6-4f61-8ff4-16eac331af39

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory.AffineQuotient
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Chart
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]
    (hf : IsFreeAction G X) : Mono (lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X)) := by
  refine ⟨fun {T} a b h ↦ ?_⟩
  have h₁ : a ≫ γ[G, X] = b ≫ γ[G, X] := by
    simpa using congr($h ≫ fst X X)
  have h₂ : a ≫ snd G X = b ≫ snd G X := by
    simpa using congr($h ≫ snd X X)
  have ea : ∀ c : T ⟶ G ⊗ X, c ≫ γ[G, X] = (c ≫ fst G X) • (c ≫ snd G X) := by
    intro c
    rw [Hom.smul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  rw [ea a, ea b, ← h₂] at h₁
  have : ((b ≫ fst G X)⁻¹ * (a ≫ fst G X)) • (a ≫ snd G X) = a ≫ snd G X := by
    rw [mul_smul, h₁, inv_smul_smul]
  have h₃ := hf _ _ _ this
  apply CartesianMonoidalCategory.hom_ext
  · exact (inv_mul_eq_one.1 h₃).symm
  · exact h₂
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
