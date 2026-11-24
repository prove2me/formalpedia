-- Prove2me | solution 1 for GlobalTheory.FormalCalc.formalLog_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:26:14.511624+00:00
-- url     : https://prove2.me/submissions/93e9de26-4fd0-4e06-a7a3-a3a74a49a34a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalLog
import Theorems.Thm_GlobalTheory_FormalCalc_mul_pderiv_formalLog
import Theorems.Thm_GlobalTheory_FormalCalc_eq_formalLog_of_pderiv
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
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
theorem _root_.solution {f g : MvPowerSeries σ A} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) : formalLog (f * g) = formalLog f + formalLog g := by
  refine (eq_formalLog_of_pderiv (by simp [hf, hg])
    (by simp [constantCoeff_formalLog hf, constantCoeff_formalLog hg]) fun i => ?_).symm
  rw [Derivation.leibniz, ← mul_pderiv_formalLog hf, ← mul_pderiv_formalLog hg, map_add,
    smul_eq_mul, smul_eq_mul]
  ring
end GlobalTheory.FormalCalc
