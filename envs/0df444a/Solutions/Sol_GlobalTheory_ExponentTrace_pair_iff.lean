-- Prove2me | solution 1 for GlobalTheory.ExponentTrace.pair_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:15:38.278798+00:00
-- url     : https://prove2.me/submissions/4ff5c26e-004b-431f-84c7-d5ab62ef6916

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmFieldHostElementAddConjEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CuspPairingIntIffHermitianExponentIntegral
import Theorems.Thm_GlobalTheory_ExponentTrace_mem_mul_inv_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_trace_dual_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_pairIdeal_ne_zero
import Theorems.Thm_GlobalTheory_ExponentTrace_ccc
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_coe_different_ne_zero
import Theorems.Thm_GlobalTheory_conjFrac_different
import Theorems.Thm_GlobalTheory_conjFrac_ne_zero
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
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.ExponentTrace
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.ExponentTrace
theorem _root_.solution {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) (x : E) :
    (∀ s ∈ pairIdeal N A B, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) ↔
      ∀ u ∈ dif E * A, ∀ m ∈ dif E * B,
        (N : E) * (u * x * cc m) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hN'
  have hc : conjFrac (dif E * B) = dif E * conjFrac B := by rw [map_mul, conjFrac_different]
  have e : (dif E)⁻¹ * (pairIdeal N A B)⁻¹ =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)⁻¹ *
        (1 * (dif E * conjFrac B)⁻¹ * (dif E * A)⁻¹) := by
    rw [← FractionalIdeal.spanSingleton_inv]
    unfold pairIdeal
    simp only [mul_inv]
    ring
  rw [trace_dual_iff (pairIdeal_ne_zero hN hA hB), e, FractionalIdeal.mem_singleton_mul]
  simp only [mem_mul_inv_iff (mul_ne_zero hd hA), mem_mul_inv_iff (mul_ne_zero hd hB')]
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu m hm
    have := hy u hu (cc m) (hc ▸ cc_mem_conjFrac.2 hm)
    convert this using 1
    field_simp
  · intro h
    refine ⟨(N : E) * x, fun u hu m hm => ?_, by field_simp⟩
    have := h u hu (cc m) (mem_conjFrac.1 (hc ▸ hm))
    rw [ccc] at this
    convert this using 1
    ring
end GlobalTheory.ExponentTrace
