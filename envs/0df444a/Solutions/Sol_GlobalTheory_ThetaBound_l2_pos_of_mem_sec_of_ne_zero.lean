-- Prove2me | solution 1 for GlobalTheory.ThetaBound.l2_pos_of_mem_sec_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:26.093511+00:00
-- url     : https://prove2.me/submissions/24834b7b-f6b3-4136-8790-bbdb0ba2f300

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_GlobalTheory_ThetaBound_l2NormSq_nonneg_gaussianTorus
import Theorems.Thm_GlobalTheory_ThetaBound_oneColumn_l2Norm_eq_torus
import Theorems.Thm_GlobalTheory_packingCount
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eq_zero_of_l2_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
open TensorLat
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (X : PT E) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1)
    (hne : s ≠ 0) : 0 < X.l2 q s := by
  refine lt_of_le_of_ne ?_ fun h => hne (eq_zero_of_l2_eq_zero X packingCount hq hs h.symm)
  rw [← oneColumn_l2Norm_eq_torus]
  exact l2NormSq_nonneg_gaussianTorus _ _ _
end GlobalTheory.ThetaBound
