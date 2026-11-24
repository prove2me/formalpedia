-- Prove2me | solution 1 for GlobalTheory.FormalCalc.formalExp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:25:53.658864+00:00
-- url     : https://prove2.me/submissions/1fd28f93-dc0a-4883-9ab1-ffe1311a0c8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalExp
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_formalExp
import Theorems.Thm_GlobalTheory_FormalCalc_eq_formalExp_of_pderiv
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
theorem _root_.solution {f g : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : formalExp (f + g) = formalExp f * formalExp g := by
  refine (eq_formalExp_of_pderiv (by simp [hf, hg])
    (by simp [constantCoeff_formalExp hf, constantCoeff_formalExp hg]) fun i => ?_).symm
  rw [Derivation.leibniz, pderiv_formalExp hf, pderiv_formalExp hg, map_add, smul_eq_mul,
    smul_eq_mul]
  ring
end GlobalTheory.FormalCalc
