-- Prove2me | solution 1 for GlobalTheory.ThetaRho.pointwiseNormSq_comp_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:48:05.961513+00:00
-- url     : https://prove2.me/submissions/c901b687-7192-44dd-b7c1-b03d7757db0b

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
theorem _root_.solution (s : (Fin 1 → Vsp T'.dim) → ℂ) (y : Vsp T.dim) :
    T.ptN2 1 (fun w => s fun k => U (w k)) (fun _ => y) = T'.ptN2 1 s fun _ => U y := by
  simp only [PT.ptN2, HC, hf_map]
end GlobalTheory.ThetaRho
