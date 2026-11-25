-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RowIrr.rowSub_rowSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:33.125807+00:00
-- url     : https://prove2.me/submissions/1ebfea49-e9e0-4300-857d-8befa276f65d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EvalBasePtTopMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame.RowIrr
theorem _root_.solution {d a : ℕ} (κ κ' : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rowSub κ (rowSub κ' P) = rowSub (fun τ => κ τ * κ' τ) P := by
  have : (rowSub κ).comp (rowSub κ') = (rowSub (fun τ => κ τ * κ' τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, rowSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this
end GlobalTheory.MinorFrame.RowIrr
