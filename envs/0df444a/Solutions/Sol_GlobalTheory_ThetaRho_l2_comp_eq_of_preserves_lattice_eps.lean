-- Prove2me | solution 1 for GlobalTheory.ThetaRho.l2_comp_eq_of_preserves_lattice_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:36.967735+00:00
-- url     : https://prove2.me/submissions/9ec4a77b-404b-4d77-95ae-fc2f3948ad2e

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
import Theorems.Thm_GlobalTheory_ThetaRho_pointwiseNormSq_comp_isometry
import Theorems.Thm_GlobalTheory_ThetaRho_comp_mem_Sec
import Theorems.Thm_GlobalTheory_TensorLat_setAverage_comp_equiv
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_continuous_pointNormSq_quotient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2_norm_fundamental_domain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointwiseNormSq_add_period
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
    (hs : s ∈ T'.Sec 1 1) : T.l2 1 (fun w => s fun k => U (w k)) = T'.l2 1 s := by
  have hF := comp_mem_Sec T T' U hL he hs
  let e : Vsp T.dim ≃L[ℝ] Vsp T'.dim :=
    (U.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hev : ∀ v, e v = U v := fun _ => rfl
  let b' := T'.b.map e.symm.toLinearEquiv
  have hrepr : ∀ v i, b'.repr v i = T'.b.repr (U v) i := fun v i => by
    simp only [b', Module.Basis.map_repr]
    rfl
  have hfd : e ⁻¹' ZSpan.fundamentalDomain T'.b = ZSpan.fundamentalDomain b' := by
    ext v
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, hev]
  have hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range T.b) := by
    intro v hv
    refine (hL v).2 ?_
    rw [Module.Basis.mem_span_iff_repr_mem] at hv ⊢
    simpa only [hrepr] using hv
  have h := average_fundamentalDomain_eq_real volume T.b b'
    (fun y => T.ptN2 1 (fun w => s fun k => U (w k)) (fun _ => y))
    ((TiledBoundaries.continuous_pointNormSq_quotient T 1 hF.1.continuous).comp (continuous_pi fun _ => continuous_id))
    (fun γ hγ v => pointwiseNormSq_add_period T hF (γ := fun _ => γ) (fun _ => hγ) (fun _ => v)) hle 0
  rw [l2_norm_fundamental_domain, l2_norm_fundamental_domain, TensorLat.setAverage_comp_equiv volume volume e, hfd, ← h]
  simp only [hev, pointwiseNormSq_comp_isometry, add_zero]
end GlobalTheory.ThetaRho
