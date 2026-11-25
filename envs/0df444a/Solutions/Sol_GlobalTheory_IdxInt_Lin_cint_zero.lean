-- Prove2me | solution 1 for GlobalTheory.IdxInt.Lin.cint_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:10.254726+00:00
-- url     : https://prove2.me/submissions/2ed196b2-6400-4e2c-a9bd-feb7858b2a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBound
import Theorems.Thm_GlobalTheory_IdxInt_Lin_fine_zero
import Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_eq_of_fineSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Lin
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Lin
theorem _root_.solution (A : AddSubgroup W) : cint A (fun _ => 0) = 0 := by
  rw [GlobalTheory.T.indexMeasureIntegral_eq_of_fineSubgroup A A _ (fine_zero A)]; simp
end GlobalTheory.IdxInt.Lin
