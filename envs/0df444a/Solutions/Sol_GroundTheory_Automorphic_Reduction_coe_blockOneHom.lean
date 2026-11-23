-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.coe_blockOneHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:05.482624+00:00
-- url     : https://prove2.me/submissions/cdbaabc1-0342-4736-892a-74b00885594e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction
variable {R : Type*} [CommRing R] {m : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (γ : GL (Fin m) R) :
    ((blockOneHom γ : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      blockOne (γ : Matrix (Fin m) (Fin m) R) := rfl
end GroundTheory.Automorphic.Reduction
