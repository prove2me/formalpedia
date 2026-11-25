-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RowIrr.eval_colSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:10.745416+00:00
-- url     : https://prove2.me/submissions/4ade29b7-f77a-40c4-ae21-37e516ad3b35

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
theorem _root_.solution {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (colSub g P) = eval (fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * z (y.1, y.2.1, j')) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p y hp => simp [colSub, hp] at *
end GlobalTheory.MinorFrame.RowIrr
