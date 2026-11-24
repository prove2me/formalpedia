-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.hTrans_zero_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:43:38.51369+00:00
-- url     : https://prove2.me/submissions/dbeb5d5f-455d-4574-8e0e-1f3a5c3dcbac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Theorems.Thm_GlobalTheory_HeckeTwoExp_phi_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution (ν y : ℝ) : hTrans 0 ν (-y) = hTrans 0 (-ν) y := by
  unfold hTrans
  conv_lhs => rw [← MeasureTheory.integral_neg_eq_self]
  congr 1; funext t
  simp only [phi_zero, ofReal_neg]
  congr 1
  · rw [show -(t : ℂ) + -(y : ℂ) * I = -((t : ℂ) + (y : ℂ) * I) by ring, inv_neg, neg_sq]
  · congr 1; ring
end GlobalTheory.HeckeTwoExp
