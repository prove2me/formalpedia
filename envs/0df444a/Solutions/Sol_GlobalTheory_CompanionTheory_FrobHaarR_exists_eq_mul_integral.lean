-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:15.037363+00:00
-- url     : https://prove2.me/submissions/455fad04-8ad0-41ef-822e-3ff68eb81f4e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_exists_open_left_stab
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_ind_left
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_exists_coeff
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_right
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_ind_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup
import Theorems.Thm_GroundTheory_Automorphic_isCompact_inf_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
namespace GlobalTheory.CompanionTheory.FrobHaarR
theorem _root_.solution :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G],
      IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ),
      (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  intro G _ _ _ _ _ _ _ _ hU μ _ L hL
  obtain ⟨K₀, hK₀⟩ := GroundTheory.Automorphic.exists_compactOpenSubgroup (G := G)
  have hI := haarForm_right hU μ
  refine ⟨L (ind K₀ hK₀) / haarForm μ (ind K₀ hK₀), fun α => ?_⟩
  rw [← haarForm_apply]
  obtain ⟨K', hK'⟩ := exists_open_left_stab α.2
  have hKc : IsCompact ((K₀ ⊓ K' : OpenSubgroup G) : Set G) :=
    GroundTheory.Automorphic.isCompact_inf_left hK₀
  obtain ⟨s, hs⟩ := exists_coeff (K₀ ⊓ K') hKc α (fun k hk x => hK' k hk.2 x)
  obtain ⟨s₀, hs₀⟩ := exists_coeff (K₀ ⊓ K') hKc (ind K₀ hK₀)
    (fun k hk x => ind_left K₀ hK₀ hk.1 x)
  have hne := haarForm_ind_ne_zero μ (K₀ ⊓ K') hKc
  have hne₀ := haarForm_ind_ne_zero μ K₀ hK₀
  have h1 := hs L hL
  have h2 := hs _ hI
  have h3 := hs₀ L hL
  have h4 := hs₀ _ hI
  rw [h1, h2, h3, h4]
  have hs₀0 : s₀ ≠ 0 := fun h => hne₀ (by rw [h4, h, zero_mul])
  field_simp
end GlobalTheory.CompanionTheory.FrobHaarR
