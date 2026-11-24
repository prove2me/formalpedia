-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eval_clearQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:51.968579+00:00
-- url     : https://prove2.me/submissions/2605a154-6adb-4c95-bf42-7bfd02063a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_denom
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_numer
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_div_mul_pow_totalDegree_clear_denominators
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
theorem _root_.solution (Q : MvPolynomial (ι × Fin a × Fin a) ℂ) (x : ι × Fin a × Fin a → ℂ)
    (hdet : ∀ τ, (1 + famOf x τ).det ≠ 0) :
    eval x (clearQ Q) = eval (fun v => cay (famOf x v.1) v.2.1 v.2.2) Q * (eval x denom) ^ Q.totalDegree := by
  have hD : eval x (denom (ι := ι) (a := a)) ≠ 0 := by
    rw [eval_denom]; exact Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ
  have hfun : (fun v : ι × Fin a × Fin a => cay (famOf x v.1) v.2.1 v.2.2) =
      fun v => eval x (numer v) / eval x denom := by
    funext v
    rw [eval_numer, eval_denom,
      ← Finset.mul_prod_erase Finset.univ (fun τ => (1 + famOf x τ).det) (Finset.mem_univ v.1)]
    have hE : ∏ τ ∈ Finset.univ.erase v.1, (1 + famOf x τ).det ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => hdet τ
    rw [cay, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    field_simp [hdet v.1, hE]
  rw [hfun, eval_div_mul_pow_totalDegree_clear_denominators Q _ _ hD]
  simp only [clearQ, map_sum, map_mul, map_prod, map_pow, eval_C]
end GlobalTheory.UnitaryZariskiDense
