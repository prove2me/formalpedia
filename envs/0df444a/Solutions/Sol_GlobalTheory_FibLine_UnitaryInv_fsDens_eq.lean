-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.fsDens_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:16.470956+00:00
-- url     : https://prove2.me/submissions/31b5e917-91ff-4305-8180-10eac1eb7ba6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.UnitaryInv
namespace GlobalTheory.FibLine.UnitaryInv
theorem _root_.solution (x : ℂ) :
    (fsDens x : ℂ) = 1 / (Real.pi * (1 + x * starRingEnd ℂ x) ^ 2) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, fsDens]; push_cast; ring
end GlobalTheory.FibLine.UnitaryInv
