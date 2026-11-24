-- Prove2me | solution 1 for GlobalTheory.FormalCalc.eq_formalLog_of_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:17.862535+00:00
-- url     : https://prove2.me/submissions/3aff48c6-c41e-4556-a658-b1e9d3c68a3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalLog
import Theorems.Thm_GlobalTheory_FormalCalc_mul_pderiv_formalLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {g u : MvPowerSeries σ A} (hg : constantCoeff g = 1)
    (hu : constantCoeff u = 0) (h : ∀ i, g * pderiv A i u = pderiv A i g) :
    u = formalLog g := by
  haveI : IsAddTorsionFree A := .of_module_rat A
  have hunit : IsUnit g := isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)
  refine pderiv.ext (fun i => hunit.mul_left_cancel ?_) (by rw [hu, constantCoeff_formalLog hg])
  rw [h, mul_pderiv_formalLog hg]
end GlobalTheory.FormalCalc
