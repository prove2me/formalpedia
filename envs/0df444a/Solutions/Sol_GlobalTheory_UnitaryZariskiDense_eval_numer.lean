-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eval_numer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:21.653351+00:00
-- url     : https://prove2.me/submissions/65e8f963-9db7-42a5-8f33-830df239e4df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_det_one_add
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_cay_entry
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
theorem _root_.solution (x : ι × Fin a × Fin a → ℂ) (v : ι × Fin a × Fin a) :
    eval x (numer v) = ((1 - famOf x v.1) * (1 + famOf x v.1).adjugate) v.2.1 v.2.2 *
      ∏ τ ∈ Finset.univ.erase v.1, (1 + famOf x τ).det := by
  simp only [numer, map_mul, map_prod, eval_det_one_add, eval_cay_entry]
end GlobalTheory.UnitaryZariskiDense
