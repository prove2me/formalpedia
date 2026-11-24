-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.TubeGood_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:19.192697+00:00
-- url     : https://prove2.me/submissions/034e7639-01ba-4b5d-a9b7-6ee21e3faa22

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine

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
theorem _root_.solution {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    {f : ℂ × ℂ → ℂ} (hf : Fac f Ω) (hF : TubeGood F Ω) :
    TubeGood (fun l g => f l • F l g) Ω := by
  refine ⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
    obtain ⟨U, hU, M₂, h₂⟩ := hF.bdd C hC hCc g
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩
    rw [norm_smul]
    exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
end GlobalTheory.CompanionTheory.RgEisGal
