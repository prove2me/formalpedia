-- Prove2me | solution 1 for GlobalTheory.ClassMin.realExtension_eq_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:45:45.806463+00:00
-- url     : https://prove2.me/submissions/597a55e2-c8b8-4104-a38d-87dc9b53e17c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
import Theorems.Thm_GlobalTheory_eq_realExt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) : realExtension Q = realExt Q :=
  eq_realExt Q _ (realExtension_one_tmul Q)
end GlobalTheory.ClassMin
