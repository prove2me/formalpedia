-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Principalise.isIso_of_isIso_comp_of_dense_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:08:36.119544+00:00
-- url     : https://prove2.me/submissions/7d4eb183-dc87-4d6d-adab-9e06b79d7b67

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupComp
import Theorems.Thm_GlobalTheory_IsSmoothBlowupSeq_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Principalise
namespace GlobalTheory.CompanionTheory.Principalise
theorem _root_.solution {A P V : Scheme.{0}} (a : A ⟶ P) (b : P ⟶ V) [IsIso (a ≫ b)]
    [IsSeparated b] [IsReduced P] (hd : Dense (Set.range a)) : IsIso b ∧ IsIso a := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : V ⟶ P, σ = inv (a ≫ b) ≫ a := ⟨_, rfl⟩
  have hσ : σ ≫ b = 𝟙 V := by simp [hσdef]
  have haσ : (a ≫ b) ≫ σ = a := by simp [hσdef]
  have hid : IsIso (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ b
  have hr : Set.range a ⊆ Set.range σ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(a ≫ b) x, by rw [← Scheme.Hom.comp_apply, haσ]⟩
  have hcl : IsClosed (Set.range σ) := σ.isClosedEmbedding.isClosed_range
  have : Surjective σ := ⟨Set.range_eq_univ.1 (by
    have h := (hd.mono hr).closure_eq
    rwa [hcl.closure_eq] at h)⟩
  have : IsIso σ := isIso_of_isClosedImmersion_of_surjective σ
  have hb : IsIso b := IsIso.of_isIso_comp_left σ b
  exact ⟨hb, IsIso.of_isIso_comp_right a b⟩
end GlobalTheory.CompanionTheory.Principalise
