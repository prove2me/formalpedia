-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eval_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:44.94879+00:00
-- url     : https://prove2.me/submissions/7e28c750-2a4e-49ca-82c3-d23b317c08f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_det_one_add
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
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
variable [Fintype ι]
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution (x : ι × Fin a × Fin a → ℂ) :
    eval x (denom (ι := ι) (a := a)) = ∏ τ, (1 + famOf x τ).det := by
  simp only [denom, map_prod, eval_det_one_add]
end GlobalTheory.UnitaryZariskiDense
