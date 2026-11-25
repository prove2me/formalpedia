-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.det_rowMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:48.377112+00:00
-- url     : https://prove2.me/submissions/e008b010-5b19-4cea-8db8-7ad386394a62

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
theorem _root_.solution (x : Fin (m + 1) → F) : (rowMatrix x).det = x (Fin.last m) := by
  rw [det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [rowMatrix, Fin.castSucc_ne_last]
  · intro i j hij
    simp only [rowMatrix, of_apply]
    have hij' : i < j := hij
    have hi : i ≠ Fin.last m := fun h => by
      rw [h] at hij'
      exact absurd hij' (not_lt.2 (Fin.le_last j))
    rw [if_neg hi, if_neg hij'.ne]
end GroundTheory.Automorphic.Reduction
