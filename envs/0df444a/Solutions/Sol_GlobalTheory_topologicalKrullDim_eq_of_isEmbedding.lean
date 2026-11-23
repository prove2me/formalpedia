-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:36.920585+00:00
-- url     : https://prove2.me/submissions/520761e9-d7a5-4527-a4ea-b9c9f0ddb346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open Topology TopologicalSpace
namespace GlobalTheory
theorem _root_.solution {W X : Type*} [TopologicalSpace W]
    [TopologicalSpace X] {e : W → X} (he : IsEmbedding e) {Z : Set X} (hZ : Set.range e = Z) :
    topologicalKrullDim Z = topologicalKrullDim W := by
  subst hZ
  exact (he.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm
end GlobalTheory
