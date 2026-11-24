-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.TubeGood_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:55.591185+00:00
-- url     : https://prove2.me/submissions/7c77a934-4d0e-4078-adaf-3ddeb7694ab8

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
variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by
  refine ⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨U, hU, M₁, h₁⟩ := hF.bdd C hC hCc g
    obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
    exact mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
end GlobalTheory.CompanionTheory.RgEisGal
