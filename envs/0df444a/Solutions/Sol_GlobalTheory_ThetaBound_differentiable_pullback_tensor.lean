-- Prove2me | solution 1 for GlobalTheory.ThetaBound.differentiable_pullback_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:39.055272+00:00
-- url     : https://prove2.me/submissions/267142a6-52d7-4543-b65d-d14a7692e92f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_diff
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
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
open TensorLat
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (X : PT E) {n : ℕ} (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : Differentiable ℂ s) :
    Differentiable ℂ (s0 X (n := n) π s) := by
  have hc : ContDiff ℂ (⊤ : ℕ∞) (s0 X (n := n) π s) := by
    refine contDiff_prod fun k _ => (contDiff_of_diff hs).comp (contDiff_pi.2 fun _ => ?_)
    exact (LinearMap.toContinuousLinearMap π).contDiff.comp (contDiff_apply ℂ (Vsp X.dim) k)
  exact hc.differentiable (by simp)
end GlobalTheory.ThetaBound
