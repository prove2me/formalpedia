-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTop.gl_locallyCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:35.163401+00:00
-- url     : https://prove2.me/submissions/7cc04ba4-af9b-4728-8051-f0b31cd309c6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_isClosedEmbedding_embedProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTop
variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisTop
theorem _root_.solution [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL ι R) := by
  have : LocallyCompactSpace (Matrix ι ι R) := inferInstanceAs (LocallyCompactSpace (ι → ι → R))
  have : LocallyCompactSpace (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isClosedEmbedding.locallyCompactSpace
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).locallyCompactSpace
end GlobalTheory.CompanionTheory.RgEisTop
