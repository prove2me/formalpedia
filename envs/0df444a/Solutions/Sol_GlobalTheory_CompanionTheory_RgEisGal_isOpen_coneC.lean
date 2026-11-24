-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.isOpen_coneC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:01:34.518904+00:00
-- url     : https://prove2.me/submissions/6941f6c9-026a-4863-8f55-75e47e322b09

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing
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
theorem _root_.solution (r : ℝ) : IsOpen (coneC r) :=
  (open_convex2 (-1) 1 0 1 1 0 r fun x => by
    simp only [coneC, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1
end GlobalTheory.CompanionTheory.RgEisGal
