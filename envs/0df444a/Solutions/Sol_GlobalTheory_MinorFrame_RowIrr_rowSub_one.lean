-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RowIrr.rowSub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:16.37271+00:00
-- url     : https://prove2.me/submissions/1ab74338-50ed-4124-8f1b-6d8180996bc9

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
theorem _root_.solution {d a : ℕ} (P : Pol ι d a) : rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) P = P := by
  have : (rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [rowSub, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single y.2.1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this
end GlobalTheory.MinorFrame.RowIrr
