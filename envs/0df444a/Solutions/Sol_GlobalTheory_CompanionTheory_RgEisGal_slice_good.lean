-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.slice_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:01:36.772868+00:00
-- url     : https://prove2.me/submissions/92ce56ed-7a4c-4dc0-b9d1-7590adcd1607

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
theorem _root_.solution {T : Type} [TopologicalSpace T] {Φ : ℂ × ℂ → T → X} (hΦ : TubeGood Φ Set.univ) :
    (∀ g, Differentiable ℂ fun y : ℂ => Φ (0, y) g) ∧
    (Continuous fun y : ℂ × T => Φ (0, y.1) y.2) ∧
    ∀ (b a : ℝ) (g : T), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U,
      ‖Φ (0, z) g'‖ ≤ M := by
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · have h₁ := hΦ.hol g 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    exact differentiableOn_univ.1 h₁
  · have hc : Continuous fun y : ℂ × T => (((0 : ℂ), y.1), y.2) := by fun_prop
    have := hΦ.cont.comp hc.continuousOn (s := Set.univ) (fun y _ => by simp [tube])
    exact continuousOn_univ.1 this
  · obtain ⟨U, hU, M, hM⟩ := hΦ.bdd (({0} : Set ℝ) ×ˢ Set.Icc b a) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc) g
    exact ⟨U, hU, M, fun z h₁ h₂ g' hg' => hM _ (slice_mem_tube ⟨h₁, h₂⟩) g' hg'⟩
end GlobalTheory.CompanionTheory.RgEisGal
