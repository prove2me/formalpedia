-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.vecMul_blockOne_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:50.473802+00:00
-- url     : https://prove2.me/submissions/edfaf4e0-1852-44fd-9f3b-9fd8672721aa

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
theorem _root_.solution (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    (y ᵥ* blockOne M) (Fin.castSucc j) = (Fin.init y ᵥ* M) j := by
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.init]
end GroundTheory.Automorphic.Reduction
