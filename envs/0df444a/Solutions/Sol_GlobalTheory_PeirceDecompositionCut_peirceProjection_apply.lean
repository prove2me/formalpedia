-- Prove2me | solution 1 for GlobalTheory.PeirceDecompositionCut.peirceProjection_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:24.059793+00:00
-- url     : https://prove2.me/submissions/6fd0d06b-c78a-4366-aa7a-b95ba3d8bd8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_OneSubSmulPeirceCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PeirceDecompositionCut
variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]
variable {A}
namespace GlobalTheory.PeirceDecompositionCut
theorem _root_.solution (e : R) (he : IsIdempotentElem e) (x : A) :
    peirceCut A e he x = e • x + (1 - e) • (1 : A) := rfl
end GlobalTheory.PeirceDecompositionCut
