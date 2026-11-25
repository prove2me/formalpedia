-- Prove2me | solution 1 for GlobalTheory.ThetaRho.hermC_eq_zero_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:35.504966+00:00
-- url     : https://prove2.me/submissions/a3e9030d-4954-4ff8-9a85-9fd89cb73041

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.ThetaRho
theorem _root_.solution (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
    {i : ℕ} (hi : i ≤ r) {y : Fin r → ℂ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun a : Fin i => e (Fin.castLE hi a)))
    (c : Fin r) (hc : i ≤ c) : hermC τ.1 X.Gm y (e c) = 0 := by
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  rw [hermC_sum_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [hermC_smul_left, he, if_neg, mul_zero]
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.2
  simp only [Fin.val_castLE] at h1
  omega
end GlobalTheory.ThetaRho
