-- Prove2me | solution 1 for GlobalTheory.FormalCalc.isUnit_formalExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:10.490154+00:00
-- url     : https://prove2.me/submissions/8def1f81-d5b3-45fb-a52d-4a549b7d8816

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalExp

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
theorem _root_.solution {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    IsUnit (formalExp f) :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_formalExp hf]; exact isUnit_one)
end GlobalTheory.FormalCalc
