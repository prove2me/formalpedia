-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.mem_Om2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:15.657849+00:00
-- url     : https://prove2.me/submissions/c45a6871-cce8-47ea-952c-374f9bc8f2e5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour

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
theorem _root_.solution {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om2 N r ↔ r < N - x.1 - x.2 ∧ r < x.2 + 1 := by
  simp only [Om2, Set.mem_preimage, chgR, affR, coneA, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
end GlobalTheory.CompanionTheory.RgEisGal
