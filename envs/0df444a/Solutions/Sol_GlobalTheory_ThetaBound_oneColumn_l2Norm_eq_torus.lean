-- Prove2me | solution 1 for GlobalTheory.ThetaBound.oneColumn_l2Norm_eq_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:02.074655+00:00
-- url     : https://prove2.me/submissions/83e5c327-e3ae-43d2-a927-56040b02c2ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_GlobalTheory_ThetaBound_oneColumn_pointwiseNorm_eq_torus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2_norm_fundamental_domain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
open TensorLat
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    (gtOf X q).l2 q (fun z => s fun _ => z) = X.l2 q s := by
  rw [l2_norm_fundamental_domain, GT.l2]
  simp only [oneColumn_pointwiseNorm_eq_torus]
  rfl
end GlobalTheory.ThetaBound
