-- Prove2me | solution 1 for GlobalTheory.ThetaRho.exists_diag_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:13.891957+00:00
-- url     : https://prove2.me/submissions/ac7f089b-7b7a-4499-a1d5-d96be698392e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaNormInvariant
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRho
open MeasureTheory
open scoped ComplexConjugate
namespace GlobalTheory.ThetaRho
theorem _root_.solution {ι ι' : Type} [Fintype ι] [Fintype ι'] (ε : ι' ≃ ι) (w : ι' → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) :
    ∃ U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι', ∀ y i, U y i = w i * y (ε i) := by
  have hw0 : ∀ i, w i ≠ 0 := fun i h => by simpa [h] using hw i
  refine ⟨{ toFun := fun y => WithLp.toLp 2 fun i => w i * y (ε i)
            invFun := fun z => WithLp.toLp 2 fun j => (w (ε.symm j))⁻¹ * z (ε.symm j)
            map_add' := fun y z => ?_
            map_smul' := fun c y => ?_
            left_inv := fun y => ?_
            right_inv := fun z => ?_
            norm_map' := fun y => ?_ }, fun y i => rfl⟩
  · ext i; simp [mul_add]
  · ext i; simp [mul_left_comm]
  · ext j; simp [hw0]
  · ext i; simp [hw0]
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← ε.sum_comp]
    simp [hw]
end GlobalTheory.ThetaRho
