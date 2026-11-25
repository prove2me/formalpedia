-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.isRegular_exElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:54.320332+00:00
-- url     : https://prove2.me/submissions/6e6b05b9-eec9-471f-8815-75b3ca13e53f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_isQuadInvol_complex
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
theorem _root_.solution :
    IsRegular (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) exElt where
  quad := isQuadInvol_complex
  herm := by ext i j; fin_cases i <;> fin_cases j <;> simp [cT]
  nondeg := by simp [Matrix.det_fin_two]
  mem := by
    show cT _ _ * _ * _ = _
    have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cT, exElt, Matrix.mul_apply, Fin.sum_univ_two, h2]
  sep := by
    have h : (exElt : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![2, 1 / 2] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [exElt]
    rw [h, Matrix.charpoly_diagonal]
    refine Polynomial.separable_prod_X_sub_C_iff.2 ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num at hij
end GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
