-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.single_last_vecMul_rowMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:49.807254+00:00
-- url     : https://prove2.me/submissions/ce125af5-003e-4c65-950c-f52fdda67a1f

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
variable {F : Type*} [Field F] {m : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (x : Fin (m + 1) → F) :
    Pi.single (Fin.last m) 1 ᵥ* rowMatrix x = x := by
  ext j
  rw [vecMul, dotProduct, Finset.sum_eq_single (Fin.last m)]
  · simp [rowMatrix]
  · intro b _ hb
    simp [hb]
  · simp
end GroundTheory.Automorphic.Reduction
