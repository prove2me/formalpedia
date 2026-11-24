-- Prove2me | solution 1 for GlobalTheory.GaussWidths.hasWidth_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:19.826805+00:00
-- url     : https://prove2.me/submissions/a549e286-3b41-4821-a5a3-ccb3a58fe1d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
import Theorems.Thm_GlobalTheory_GaussWidths_hasWidth_of_lt
import Theorems.Thm_GlobalTheory_GaussWidths_hasWidth_fourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory.GaussWidths
theorem _root_.solution {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M)
    (hF : ∀ f ∈ M, 𝓕 f ∈ M) (hπ : HasWidth M Real.pi) (c : ℝ) (hc : 0 < c) : HasWidth M c := by
  rcases lt_trichotomy c Real.pi with hlt | heq | hgt
  · exact hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt
  · exact heq ▸ hπ
  · have hc' : 0 < Real.pi ^ 2 / c := by positivity
    have hlt : Real.pi ^ 2 / c < Real.pi := by
      rw [div_lt_iff₀ hc]; nlinarith [Real.pi_pos]
    have h1 := hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)
    have : Real.pi ^ 2 / (Real.pi ^ 2 / c) = c := by
      have := Real.pi_pos.ne'; field_simp
    rwa [this] at h1
end GlobalTheory.GaussWidths
