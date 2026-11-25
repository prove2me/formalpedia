-- Prove2me | solution 1 for GlobalTheory.TensorLat.norm_sq_contr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:56.376489+00:00
-- url     : https://prove2.me/submissions/a0aea411-9cc6-4ec5-9227-ec37e36a4909

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Theorems.Thm_GlobalTheory_TensorLat_norm_sq_contr_apply_le
import Theorems.Thm_GlobalTheory_TensorLat_norm_sq_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (γ : Fin n → Vsp dim) (w : Fin n → E) {R : ℝ}
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ R) :
    ‖contr γ w‖ ^ 2 ≤ R * ‖flat γ‖ ^ 2 := by
  rw [norm_sq_flat, EuclideanSpace.norm_sq_eq]
  simp only [EuclideanSpace.norm_sq_eq (γ _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (norm_sq_contr_apply_le γ w i).trans ?_
  exact mul_le_mul_of_nonneg_right (hw i.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
end GlobalTheory.TensorLat
