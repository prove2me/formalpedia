-- Prove2me | solution 1 for GlobalTheory.Reg.IdemCusp.flow_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:08:12.691879+00:00
-- url     : https://prove2.me/submissions/262ccdad-beb6-4971-99c9-1f45b3d125c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IdemMulMemCusp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_cont_flowL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_flowL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_flow_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_flow_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.IdemCusp
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Reg.IdemCusp
theorem _root_.solution (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    χ (X.flow ξ (fun τ => (s τ : ℂ)) x) = χ x := by
  have hpath : Continuous fun t : ℝ => CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x :=
    ((CuspCoefficientFlow.cont_flowL X ξ).comp
      (continuous_pi fun τ => continuous_id.mul continuous_const)).clm_apply continuous_const
  have hin : ∀ t : ℝ, CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x ∈ X.dom := fun t => by
    rw [CuspCoefficientFlow.flowL_apply]
    exact (FlowCoefficientBounds.flow_real X hξ hx (fun τ => t * s τ) 0).1
  set g : ℝ → ℂ := fun t => χ (CuspCoefficientFlow.flowL X ξ (fun τ => t * s τ) x) with hg
  have hcont : Continuous g := hχ.2.1.continuousOn.comp_continuous hpath hin
  have hzo : ∀ t : ℝ, g t = 0 ∨ g t = 1 := fun t => hχ.1 _ (hin t)

  have hre : Continuous fun t => (g t).re := Complex.continuous_re.comp hcont
  have hsame : g 1 = g 0 := by
    by_contra hne
    have hhalf : (1 / 2 : ℝ) ∈ Set.uIcc (g 0).re (g 1).re := by
      rcases hzo 0 with h0 | h0 <;> rcases hzo 1 with h1 | h1 <;>
        simp_all <;> norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hre.continuousOn hhalf
    rcases hzo t with h | h <;> simp [h] at ht
  have h1 : g 1 = χ (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, one_mul]
  have h0 : g 0 = χ x := by
    simp only [hg, CuspCoefficientFlow.flowL_apply, zero_mul, Complex.ofReal_zero]
    exact congrArg χ (EmbeddingHermitianPairs.flow_zero X ξ x)
  rw [← h1, hsame, h0]
end GlobalTheory.Reg.IdemCusp
