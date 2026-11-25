-- Prove2me | solution 1 for GlobalTheory.ThetaBound.le_firstMinimum_of_period_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:42.245276+00:00
-- url     : https://prove2.me/submissions/f6970fcb-579c-41e5-9086-4eba2ac014ba

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
theorem _root_.solution (Y : GT ι) (hι : Fintype.card ι ≠ 0) {lam : ℝ}
    (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖) : lam ≤ Y.la1 := by
  refine le_csInf ⟨‖Y.b ⟨0, by omega⟩‖, Y.b ⟨0, by omega⟩,
    Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩ ?_
  rintro t ⟨x, hx, hx0, rfl⟩
  exact hmin x hx hx0
end GlobalTheory.ThetaBound
