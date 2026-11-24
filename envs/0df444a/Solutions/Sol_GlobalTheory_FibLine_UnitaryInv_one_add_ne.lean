-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.one_add_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:20.389063+00:00
-- url     : https://prove2.me/submissions/31a8e752-7cd1-4300-b671-5ca60eb3d4de

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
theorem _root_.solution (x : ℂ) : 1 + x * starRingEnd ℂ x ≠ 0 := by
  rw [Complex.mul_conj]
  have := Complex.normSq_nonneg x
  exact_mod_cast (by linarith : (1 + Complex.normSq x) ≠ 0)
end GlobalTheory.FibLine.UnitaryInv
