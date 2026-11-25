-- Prove2me | solution 1 for GlobalTheory.Reg.IdemCusp.mul_mem_SS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:52:09.590035+00:00
-- url     : https://prove2.me/submissions/f4567ae5-0202-43ea-9268-6edc5e113408

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
import Theorems.Thm_GlobalTheory_Reg_IdemCusp_fj_mul
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
theorem _root_.solution (X : Data E r) {χ : Frame X.Ψ r → ℂ} (hχ : IsIdemFn X χ) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : χ * P ∈ X.SS la := by
  simp only [Data.SS, Set.mem_ofPred_eq] at hP ⊢
  obtain ⟨⟨⟨hd, hB, hΓ⟩, C, hC⟩, hcusp⟩ := hP
  refine ⟨⟨⟨hχ.2.1.mul hd, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C, fun x hx => ?_⟩,
    fun ξ hξ x hx => ?_⟩
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.1 x hx b hb, hB x hx b hb]
    ring
  · simp only [Pi.mul_apply]
    rw [hχ.2.2.2 γ hγ x hx, hΓ γ hγ x hx]
    ring
  · have hnorm : X.pnorm la (χ * P) x = ‖χ x‖ * X.pnorm la P x := by
      simp only [Data.pnorm, Pi.mul_apply, norm_mul, mul_assoc]
    have h1 : ‖χ x‖ ≤ 1 := by
      rcases hχ.1 x hx with h | h <;> simp [h]
    have h0 : 0 ≤ X.pnorm la P x := by
      unfold Data.pnorm
      positivity
    rw [hnorm]
    exact (mul_le_of_le_one_left h0 h1).trans (hC x hx)
  · rw [fj_mul X hχ la hξ P hx, hcusp ξ hξ x hx, mul_zero]
end GlobalTheory.Reg.IdemCusp
