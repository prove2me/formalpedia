-- Prove2me | solution 1 for GlobalTheory.FibLine.hPoly_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:05.308273+00:00
-- url     : https://prove2.me/submissions/89e46fff-1da7-4123-be16-3ca1665dbd7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution (k : ℕ) : hPoly (k + 2) = X 0 * hPoly (k + 1) - X 1 * hPoly k := rfl
end GlobalTheory.FibLine
