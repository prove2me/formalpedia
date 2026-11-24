-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.mapMatrix_varMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:29.85059+00:00
-- url     : https://prove2.me/submissions/0f1e4022-4695-4a0e-978d-fa42256e196a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
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
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution (x : ι × Fin a × Fin a → ℂ) (τ : ι) :
    (eval x).mapMatrix (varMat (a := a) τ) = famOf x τ := by
  ext i j; simp [varMat, famOf]
end GlobalTheory.UnitaryZariskiDense
