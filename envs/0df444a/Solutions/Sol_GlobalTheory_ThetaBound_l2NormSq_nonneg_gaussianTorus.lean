-- Prove2me | solution 1 for GlobalTheory.ThetaBound.l2NormSq_nonneg_gaussianTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:45:12.977577+00:00
-- url     : https://prove2.me/submissions/04269562-b877-44a7-a14a-318a759e6259

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd

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
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : 0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.average_eq]
  refine MeasureTheory.integral_nonneg_of_ae ?_ |> smul_nonneg (by positivity)
  refine Filter.Eventually.of_forall fun v => ?_
  unfold GT.ptN2
  positivity
end GlobalTheory.ThetaBound
