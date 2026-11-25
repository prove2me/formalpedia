-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.schur_translations_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:48.448824+00:00
-- url     : https://prove2.me/submissions/7b730593-3500-459e-89ca-2493b2de80ee

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SchurChar
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}
namespace GlobalTheory.CompanionTheory.SW.SchurChar
theorem _root_.solution (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V) (h : NADual V χ μ) (T : (V → ℂ) → (V → ℂ))
    (hSB : ∀ φ, SB φ → SB (T φ))
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hchar : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) :
    ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by
  have hloc := fun {φ : V → ℂ} (hφ : SB φ) {x : V} (hx : φ x = 0) =>
    apply_eq_zero h hadd hsmul hchar hφ hx
  obtain ⟨hTG, hT2, -, -, -, -, -, hcover, -⟩ := h
  haveI := hTG
  haveI := hT2
  obtain ⟨L, hLc, hLo, -⟩ := hcover 0
  classical
  set φ₀ : V → ℂ := (L : Set V).indicator (fun _ => 1) with hφ₀
  have hφ₀lc : IsLocallyConstant φ₀ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u
    by_cases hu : u ∈ (L : Set V)
    · exact ⟨L, hLo, hu, fun v hv => by
        rw [hφ₀, Set.indicator_of_mem hv, Set.indicator_of_mem hu]⟩
    · exact ⟨(L : Set V)ᶜ, hLc.isClosed.isOpen_compl, hu, fun v hv => by
        rw [hφ₀, Set.indicator_of_notMem hv, Set.indicator_of_notMem hu]⟩
  have hφ₀SB : SB φ₀ :=
    ⟨hφ₀lc, HasCompactSupport.intro hLc fun u hu => Set.indicator_of_notMem hu _⟩
  have hφ₀0 : φ₀ 0 = 1 := Set.indicator_of_mem L.zero_mem _
  refine ⟨T φ₀ 0, fun φ hφ => ?_⟩
  funext x
  set φ₁ : V → ℂ := fun u => φ₀ (u + -x) with hφ₁
  have hφ₁SB : SB φ₁ :=
    ⟨hφ₀SB.1.comp_continuous (continuous_add_right _),
      hφ₀SB.2.comp_homeomorph (Homeomorph.addRight (-x))⟩
  have hψ := sb_add hφ (sb_smul (-φ x) hφ₁SB)
  have hz : (φ + (-φ x) • φ₁) x = 0 := by
    simp [hφ₁, hφ₀0]
  have h1 := hloc hψ hz
  rw [hadd _ _ hφ (sb_smul _ hφ₁SB), hsmul _ _ hφ₁SB, htr (-x) φ₀ hφ₀SB] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_neg_cancel] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination h1
end GlobalTheory.CompanionTheory.SW.SchurChar
