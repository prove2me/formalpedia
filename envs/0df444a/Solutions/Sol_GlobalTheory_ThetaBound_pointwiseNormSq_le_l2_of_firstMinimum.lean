-- Prove2me | solution 1 for GlobalTheory.ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:22.246569+00:00
-- url     : https://prove2.me/submissions/2bad0942-f668-41db-b22f-5261d416f9cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_GlobalTheory_ThetaBound_l2NormSq_nonneg_gaussianTorus
import Theorems.Thm_GlobalTheory_ThetaBound_le_firstMinimum_of_period_lower_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
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
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (hsup : GSupStatement) (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F v ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) ^ 2 * Y.l2 1 F := by
  refine (hsup ι Y 1 le_rfl F hF v).trans (mul_le_mul_of_nonneg_right ?_ (l2NormSq_nonneg_gaussianTorus Y 1 F))
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm (Fintype.card ι) 2]
  simp only [Nat.cast_one, one_pow, mul_one, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  have h1 := le_firstMinimum_of_period_lower_bound Y hι hmin
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : 0 < Y.la1 := hlam.trans_le h1
  gcongr
end GlobalTheory.ThetaBound
