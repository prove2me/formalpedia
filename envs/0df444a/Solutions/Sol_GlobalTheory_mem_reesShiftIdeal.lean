-- Prove2me | solution 1 for GlobalTheory.mem_reesShiftIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:05.851129+00:00
-- url     : https://prove2.me/submissions/8ed7bf46-af53-47eb-affa-7e84afa1d58b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {I : Ideal R} (p : reesAlgebra I) :
    p ∈ reesShiftIdeal I ↔ ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1) := Iff.rfl
end GlobalTheory
