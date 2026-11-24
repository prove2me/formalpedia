-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:57.916818+00:00
-- url     : https://prove2.me/submissions/d795bf15-29f9-4b6e-bfbf-a3dcd60d8641

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvariance
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_shiftFst_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by
  have h := shiftFst_integrable hG hs t hsm
  unfold phi
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod_symm _ h
end GlobalTheory.CompanionTheory.TubeFourier
