-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.stripEntire_of_fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:01:38.258277+00:00
-- url     : https://prove2.me/submissions/7ce49940-27e6-4444-805e-a21d7c03a18b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_line_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_slice_mem_tube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {f : ℂ → X} {A : ℂ × ℂ → X} (hA : Fac A Set.univ)
    (h : ∀ y, f y = A (0, y)) : StripEntire f := by
  refine ⟨?_, fun b c => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact differentiableOn_univ.1 h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩
end GlobalTheory.CompanionTheory.RgEisGal
