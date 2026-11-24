-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.entire_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:18.720604+00:00
-- url     : https://prove2.me/submissions/a4f364c0-6477-421d-9bb6-ac5684eeb100

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {f g : ℂ → X}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (R : ℝ) (h : ∀ z : ℂ, R < z.re → f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  refine hfa.eq_of_eventuallyEq hga (z₀ := ((R + 1 : ℝ) : ℂ)) ?_
  have hopen : IsOpen {z : ℂ | R < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ {z : ℂ | R < z.re} := by simp
  filter_upwards [hopen.mem_nhds hmem] with z hz using h z hz
end GlobalTheory.CompanionTheory.RgEis
