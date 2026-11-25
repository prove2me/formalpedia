-- Prove2me | solution 1 for GlobalTheory.FormalCalc.formalLog_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:11.569487+00:00
-- url     : https://prove2.me/submissions/93af30ec-379f-4e8b-aaf5-b37f90351c48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_prod
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
theorem _root_.solution (n : ℕ) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    formalLog (g ^ n) = n • formalLog g := by
  simpa using formalLog_prod (Finset.range n) (g := fun _ => g) fun _ _ => hg
end GlobalTheory.FormalCalc
