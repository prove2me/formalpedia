-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.isOpen_V34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:54.687117+00:00
-- url     : https://prove2.me/submissions/bfbb0a6d-d3fd-4ca2-a430-ce5a055b940d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_open_convex2

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
theorem _root_.solution (M : ℝ) : IsOpen (chamberPairFourLast M) :=
  (open_convex2 0 (-1) 0 (-1) 0 0 M fun x => by
    simp only [chamberPairFourLast, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1
end GlobalTheory.CompanionTheory.RgEisGal
