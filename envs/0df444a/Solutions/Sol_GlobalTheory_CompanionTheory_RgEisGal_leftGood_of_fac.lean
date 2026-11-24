-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.leftGood_of_fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:01:41.715559+00:00
-- url     : https://prove2.me/submissions/cdf33fdc-0ff0-4d46-ac2d-914b37c5592a

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
theorem _root_.solution {f : ℂ → X} {A : ℂ × ℂ → X} {a : ℝ} (hA : Fac A {x | x.2 < a})
    (h : ∀ y, f y = A (0, y)) : LeftGood f a := by
  refine ⟨?_, fun b c hc => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube {x : ℝ × ℝ | x.2 < a}} = {z | z.re < a} := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c)
      (by rintro x ⟨-, hx⟩; exact lt_of_le_of_lt hx.2 hc)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩
end GlobalTheory.CompanionTheory.RgEisGal
