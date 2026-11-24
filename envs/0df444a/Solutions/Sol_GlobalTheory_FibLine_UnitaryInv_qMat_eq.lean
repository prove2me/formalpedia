-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.qMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:23.121389+00:00
-- url     : https://prove2.me/submissions/8b8f910e-147e-4be0-a0d1-9b230074da89

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
theorem _root_.solution (H : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    qMat H x = (H 0 0 + H 0 1 * x + H 1 0 * starRingEnd ℂ x + H 1 1 * (x * starRingEnd ℂ x)) /
      (1 + x * starRingEnd ℂ x) := by
  have : ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) = 1 + x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp only [qMat, qCoef, entries, lineVec, Fintype.sum_prod_type, Fin.sum_univ_two, this, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
  ring
end GlobalTheory.FibLine.UnitaryInv
