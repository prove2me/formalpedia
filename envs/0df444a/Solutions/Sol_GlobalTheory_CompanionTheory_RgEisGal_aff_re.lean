-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.aff_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:03.310774+00:00
-- url     : https://prove2.me/submissions/d96cfe31-e2de-4d3d-a26a-30a121481815

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
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by
  simp [aff, affR]
end GlobalTheory.CompanionTheory.RgEisGal
