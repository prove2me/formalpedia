-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.vecMul_blockOne_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:51.306163+00:00
-- url     : https://prove2.me/submissions/ffd7a4a1-90b6-4d4a-b248-df68f5cbedbe

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
theorem _root_.solution (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) :
    (y ᵥ* blockOne M) (Fin.last m) = y (Fin.last m) := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc]
end GroundTheory.Automorphic.Reduction
