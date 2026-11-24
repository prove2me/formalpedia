-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.isOpen_V12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:53.244176+00:00
-- url     : https://prove2.me/submissions/b43d5300-779c-41b2-8142-3a516c5f4552

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
theorem _root_.solution (M : ℝ) : IsOpen (chamberPairTwoThree M) :=
  (open_convex2 (-1) (-1) 0 1 2 0 M fun x => by
    simp only [chamberPairTwoThree, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1
end GlobalTheory.CompanionTheory.RgEisGal
