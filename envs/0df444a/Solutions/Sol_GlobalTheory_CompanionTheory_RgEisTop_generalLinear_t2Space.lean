-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTop.generalLinear_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:33.649793+00:00
-- url     : https://prove2.me/submissions/df0c6f73-7368-4075-b61f-6ab399031969

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
theorem _root_.solution [T2Space R] : T2Space (GL ι R) :=
  (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.t2Space
end GlobalTheory.CompanionTheory.RgEisTop
