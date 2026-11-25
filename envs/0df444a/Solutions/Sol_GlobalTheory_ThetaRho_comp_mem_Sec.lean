-- Prove2me | solution 1 for GlobalTheory.ThetaRho.comp_mem_Sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:59.992968+00:00
-- url     : https://prove2.me/submissions/736ea75a-babb-48f3-8f74-28e847f494e6

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
import Theorems.Thm_GlobalTheory_ThetaRho_hf_map
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRho
open MeasureTheory
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (T T' : PT E) (U : Vsp T.dim ≃ₗᵢ[ℂ] Vsp T'.dim)
namespace GlobalTheory.ThetaRho
theorem _root_.solution (hL : ∀ y, y ∈ T.L ↔ U y ∈ T'.L)
    (he : ∀ y ∈ T.L, T'.eps (U y) = T.eps y) {s : (Fin 1 → Vsp T'.dim) → ℂ}
    (hs : s ∈ T'.Sec 1 1) : (fun w => s fun k => U (w k)) ∈ T.Sec 1 1 := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun k =>
    U.toContinuousLinearEquiv.differentiable.comp (differentiable_apply k)), fun γ hγ v => ?_⟩
  have h := hs.2 (fun k => U (γ k)) (fun k => (hL _).1 (hγ k)) (fun k => U (v k))
  have e : (fun k => U ((v + γ) k)) = (fun k => U (v k)) + fun k => U (γ k) := by
    funext k; simp
  simp only [e]
  rw [h]
  simp only [HC, hf_map, he _ (hγ _)]
end GlobalTheory.ThetaRho
