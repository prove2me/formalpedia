-- Prove2me | solution 1 for GlobalTheory.UpperHalfImaginaryForm.upper_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:35.433282+00:00
-- url     : https://prove2.me/submissions/f75d2fd7-b68a-4bf9-81d6-a967896b2dd1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_imForm_swap
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_upper_basis
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
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
variable {n : ℕ}
namespace GlobalTheory.UpperHalfImaginaryForm
theorem _root_.solution (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (x y : EuclideanSpace ℂ ι) :
    imForm x y = upper b x y - upper b y x := by
  have key : imForm = upper b - (upper b).flip := by
    refine b.ext fun i => b.ext fun j => ?_
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, upper_basis]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      have := imForm_swap (b i) (b i)
      simp only [lt_irrefl, if_false, sub_zero]
      linarith
    · have := imForm_swap (b j) (b i)
      simp only [h, lt_asymm h, if_true, if_false, zero_sub]
      linarith
  rw [key]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply]
end GlobalTheory.UpperHalfImaginaryForm
