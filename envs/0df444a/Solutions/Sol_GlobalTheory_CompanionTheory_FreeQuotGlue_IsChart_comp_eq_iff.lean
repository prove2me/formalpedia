-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.comp_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:32:59.24191+00:00
-- url     : https://prove2.me/submissions/48506248-1fbc-49a0-892c-7d7e8417d108

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
namespace IsChart
theorem _root_.solution (h : IsChart a b V q) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ V.toScheme) :
    g₁ ≫ q = g₂ ≫ q ↔ ∃ l : Z ⟶ P, l ≫ a = g₁ ≫ V.ι ∧ l ≫ b = g₂ ≫ V.ι := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := h
  constructor
  · intro e
    refine ⟨hp.lift g₁ g₂ e ≫ (b ⁻¹ᵁ V).ι, ?_, ?_⟩
    · rw [Category.assoc, ← ha, hp.lift_fst_assoc]
    · rw [Category.assoc, ← morphismRestrict_ι, hp.lift_snd_assoc]
  · rintro ⟨l, h1, h2⟩
    have hr : Set.range l ⊆ Set.range (b ⁻¹ᵁ V).ι := by
      rintro _ ⟨z, rfl⟩
      have : b (l z) ∈ V := by
        have : b (l z) = V.ι (g₂ z) := congr($h2 z)
        rw [this]; exact (g₂ z).2
      simpa using this
    let l' : Z ⟶ (b ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ l hr
    have hl : l' ≫ (b ⁻¹ᵁ V).ι = l := IsOpenImmersion.lift_fac _ _ _
    have e1 : l' ≫ a' = g₁ := by
      rw [← cancel_mono V.ι, Category.assoc, ha, reassoc_of% hl, h1]
    have e2 : l' ≫ (b ∣_ V) = g₂ := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hl, h2]
    rw [← e1, ← e2, Category.assoc, Category.assoc, hp.w]
end IsChart
end GlobalTheory.CompanionTheory.FreeQuotGlue
