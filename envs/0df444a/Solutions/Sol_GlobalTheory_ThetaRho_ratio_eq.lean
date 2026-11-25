-- Prove2me | solution 1 for GlobalTheory.ThetaRho.ratio_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:19.148494+00:00
-- url     : https://prove2.me/submissions/8569c4c3-554a-49f0-b6ad-7da922ed1bf2

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
import Theorems.Thm_GlobalTheory_ThetaRho_exists_eq_smul
import Theorems.Thm_GlobalTheory_ThetaRho_pointwiseNormSq_comp_isometry
import Theorems.Thm_GlobalTheory_ThetaRho_comp_mem_Sec
import Theorems.Thm_GlobalTheory_ThetaRho_l2_comp_eq_of_preserves_lattice_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2_smul
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
    (he : ∀ y ∈ T.L, T'.eps (U y) = T.eps y) {s : (Fin 1 → Vsp T.dim) → ℂ}
    {s' : (Fin 1 → Vsp T'.dim) → ℂ} (hs : s ∈ T.Sec 1 1) (hs0 : s ≠ 0)
    (hs' : s' ∈ T'.Sec 1 1) (hs0' : s' ≠ 0) (y : Vsp T.dim) :
    T'.ptN2 1 s' (fun _ => U y) / T'.l2 1 s' = T.ptN2 1 s (fun _ => y) / T.l2 1 s := by
  obtain ⟨c, hc⟩ := exists_eq_smul T hs (comp_mem_Sec T T' U hL he hs') hs0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hs0'
    funext w
    have := congrFun hc fun k => U.symm (w k)
    simpa using this
  rw [← pointwiseNormSq_comp_isometry, ← l2_comp_eq_of_preserves_lattice_eps T T' U hL he hs', hc, l2_smul]
  have : T.ptN2 1 (c • s) (fun _ => y) = ‖c‖ ^ 2 * T.ptN2 1 s (fun _ => y) := by
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc]
  rw [this, mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hc0))]
end GlobalTheory.ThetaRho
