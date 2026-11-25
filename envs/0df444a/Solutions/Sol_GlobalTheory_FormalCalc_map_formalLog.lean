-- Prove2me | solution 1 for GlobalTheory.FormalCalc.map_formalLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:20.013191+00:00
-- url     : https://prove2.me/submissions/523e1ea1-3efc-445c-8324-31bb18d3b89c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalLog
import Theorems.Thm_GlobalTheory_FormalCalc_mul_pderiv_formalLog
import Theorems.Thm_GlobalTheory_FormalCalc_eq_formalLog_of_pderiv
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_map

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
theorem _root_.solution (φ : A →+* B) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    map φ (formalLog g) = formalLog (map φ g) := by
  refine eq_formalLog_of_pderiv (by simp [hg]) (by simp [constantCoeff_formalLog hg]) fun i => ?_
  rw [pderiv_map, pderiv_map, ← map_mul, mul_pderiv_formalLog hg]
end GlobalTheory.FormalCalc
