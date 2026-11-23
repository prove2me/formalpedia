-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.Fac_strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:43.746814+00:00
-- url     : https://prove2.me/submissions/d26aebb5-cb58-44b8-8fda-f352404f32ea

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_aff_re
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_continuous_aff
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_continuous_affR
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_differentiable_aff_line
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_exists_bounds

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
theorem _root_.solution {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by
  refine ⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩
  · exact (hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn
  · exact (hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, -, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y)
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2
end GlobalTheory.CompanionTheory.RgEisGal
