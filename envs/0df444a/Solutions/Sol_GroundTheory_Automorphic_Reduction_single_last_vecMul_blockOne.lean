-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.single_last_vecMul_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:49.190206+00:00
-- url     : https://prove2.me/submissions/8cb46fa7-2265-4bca-9020-53f5df3b9f21

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Theorems.Thm_GroundTheory_Automorphic_Reduction_coe_blockOneHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Reduction.coe_blockOneHom

set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction
variable {R : Type*} [CommRing R] {m : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (M : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* blockOne M = Pi.single (Fin.last m) 1 := by
  ext j
  induction j using Fin.lastCases <;>
    simp [vecMul, dotProduct, Pi.single_apply, Fin.castSucc_ne_last]
end GroundTheory.Automorphic.Reduction
