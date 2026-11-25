-- Prove2me | solution 1 for GlobalTheory.TensorLat.norm_contr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:39:55.49645+00:00
-- url     : https://prove2.me/submissions/9773d44b-538f-45c5-9122-fb57fbbb6397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Theorems.Thm_GlobalTheory_TensorLat_norm_sq_contr_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (γ : Fin n → Vsp dim) (w : Fin n → E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ ρ ^ 2) :
    ‖contr γ w‖ ≤ ρ * ‖flat γ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow]
  exact norm_sq_contr_le γ w hw
end GlobalTheory.TensorLat
