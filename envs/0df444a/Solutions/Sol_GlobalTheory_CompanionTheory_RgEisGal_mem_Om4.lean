-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.mem_Om4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:22.583219+00:00
-- url     : https://prove2.me/submissions/9ed24f19-2d73-4884-95d8-0eb17bad8070

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
theorem _root_.solution {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om4 N r ↔ (r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1) ∧ x.1 < 1 / 2 := by
  simp only [Om4, Set.mem_inter_iff, Set.mem_preimage, chgR, affR, coneI, Set.mem_setOf_eq]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> refine ⟨⟨?_, ?_⟩, h₃⟩ <;> linarith
end GlobalTheory.CompanionTheory.RgEisGal
