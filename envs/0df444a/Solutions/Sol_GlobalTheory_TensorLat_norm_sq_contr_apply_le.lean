-- Prove2me | solution 1 for GlobalTheory.TensorLat.norm_sq_contr_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:44.3054+00:00
-- url     : https://prove2.me/submissions/9c17d030-b93e-4d88-b4b4-64c39b0b0835

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Theorems.Thm_GlobalTheory_TensorLat_contr_apply
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
theorem _root_.solution (γ : Fin n → Vsp dim) (w : Fin n → E) (i : Idx dim) :
    ‖contr γ w i‖ ^ 2 ≤ (∑ k, ‖i.1 (w k)‖ ^ 2) * ∑ k, ‖γ k i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖i.1 (w k)‖)
    fun k => ‖γ k i‖)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [contr_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp
end GlobalTheory.TensorLat
