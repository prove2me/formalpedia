-- Prove2me | solution 1 for GlobalTheory.UpperHalfImaginaryForm.imForm_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:03.664748+00:00
-- url     : https://prove2.me/submissions/d1cb5e4f-f40f-4fea-ac04-1a39c627f5d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_imForm_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperHalfImaginaryForm
open ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.UpperHalfImaginaryForm
theorem _root_.solution (x y : EuclideanSpace ℂ ι) : imForm y x = -imForm x y := by
  have h : Hf y x = starRingEnd ℂ (Hf x y) := by
    simp [Hf, map_sum, mul_comm]
  rw [imForm_apply, imForm_apply, h, Complex.conj_im]
end GlobalTheory.UpperHalfImaginaryForm
