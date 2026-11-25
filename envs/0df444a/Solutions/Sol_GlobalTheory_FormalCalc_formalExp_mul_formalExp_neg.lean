-- Prove2me | solution 1 for GlobalTheory.FormalCalc.formalExp_mul_formalExp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:09.94638+00:00
-- url     : https://prove2.me/submissions/dc02d8e1-301c-473a-b519-b648b5aab1b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one

set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    formalExp f * formalExp (-f) = 1 := by
  rw [← formalExp_add hf (by simp [hf]), add_neg_cancel, formalExp_zero]
end GlobalTheory.FormalCalc
