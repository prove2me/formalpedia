-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.div_fractions_bilinear_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:13.419292+00:00
-- url     : https://prove2.me/submissions/22a86b98-3716-4419-a028-249abb68e2be

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
theorem _root_.solution (h0 h1 h2 h3 A B C D N : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hN : N ≠ 0) :
    (h0 + h1 * (C / A) + h2 * (D / B) + h3 * (C / A * (D / B))) / (N / (A * B))
      = (h0 * (A * B) + h1 * (C * B) + h2 * (D * A) + h3 * (C * D)) / N := by
  field_simp
end GlobalTheory.FibLine.UnitaryInv
