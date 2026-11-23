-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.det_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:25.833542+00:00
-- url     : https://prove2.me/submissions/d56ba199-a176-482d-b561-de591c4a9f39

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
theorem _root_.solution (z : ℂ) : (z • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq z := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply, ContinuousLinearMap.det]
  congr 1
end GlobalTheory.FibLine.UnitaryInv
