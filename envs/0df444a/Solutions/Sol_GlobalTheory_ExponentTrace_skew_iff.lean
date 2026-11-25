-- Prove2me | solution 1 for GlobalTheory.ExponentTrace.skew_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:51:51.4127+00:00
-- url     : https://prove2.me/submissions/9cd56a60-4aae-42da-8de9-9643cb15f0e9

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
import Theorems.Thm_GlobalTheory_ExponentTrace_ccm
import Theorems.Thm_GlobalTheory_ExponentTrace_cca
import Theorems.Thm_GlobalTheory_ExponentTrace_ccc
import Theorems.Thm_GlobalTheory_ExponentTrace_prE_int_iff
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
import Theorems.Thm_GlobalTheory_DiagDifferent_trace_even_real_iff
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_mem_one_fractionalIdeal_iff
import Theorems.Thm_GlobalTheory_trace_cc
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
theorem _root_.solution (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {r ρ : ℕ} (X : Data E r)
    (I : Fin ρ → Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ a b, ∀ s ∈ I a b, cc s ∈ I b a)
    (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : FJ.IsHermE χ) :
    (∀ β, FJ.IsSkew β → (∀ a b, β a b / X.ξ0 ∈ I a b) → ∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∀ a b, ∀ s ∈ I a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * s) = n := by
  have hξ := X.ξ0_ne
  have hc0 : cc (0 : E) = 0 := map_zero _
  simp only [prE_int_iff]
  constructor
  · intro h a b s hs
    let S : Matrix (Fin ρ) (Fin ρ) E := Matrix.of fun i j =>
      (if a = i ∧ b = j then s else 0) + (if b = i ∧ a = j then cc s else 0)
    have hS : ∀ i j, (X.ξ0 • S) i j / X.ξ0 = S i j := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hξ]
    obtain ⟨n, hn⟩ := h (X.ξ0 • S) (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul, S, Matrix.of_apply, ccm, cca, X.ξ0_im,
        apply_ite cc, ccc, hc0, and_comm (a := a = j), and_comm (a := b = j)]
      ring) (fun i j => by
      rw [hS]
      refine Submodule.add_mem (I i j : Submodule (𝓞 E) E) ?_ ?_
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hs
        · exact zero_mem _
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hI _ _ s hs
        · exact zero_mem _)
    refine ⟨n, ?_⟩
    have e : ∑ i, ∑ j, χ i j * ((X.ξ0 • S) i j / X.ξ0) = χ a b * s + cc (χ a b * s) := by
      simp only [hS]
      simp only [S, Matrix.of_apply, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, mul_zero]
      rw [ccm, hχ a b]
      simp
    rw [e, map_add, trace_cc] at hn
    linarith
  · intro h β hβ hm
    have hreal : cc (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
      have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
      have h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hβ
      have h3 : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      simp only [cc, map_sum, map_mul, map_div₀, h1, h2, h3, neg_div_neg_eq]
      rw [Finset.sum_comm]
    have := (DiagDifferent.trace_even_real_iff E H 1 _ (fun a ha =>
      mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 ha))) hreal).2
      (fun o ho => ?_) 1 (FractionalIdeal.one_mem_one _) (map_one _)
    · rwa [mul_one] at this
    · have hh : ∀ a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * (β a b / X.ξ0 * o)) = n := fun a b =>
        h a b _ (by
          have := FractionalIdeal.mul_mem_mul (hm a b) ho
          rwa [mul_one] at this)
      choose k hk using hh
      refine ⟨∑ a, ∑ b, k a b, ?_⟩
      simp only [Finset.sum_mul, map_sum, mul_assoc, hk]
      push_cast
      rfl
end GlobalTheory.ExponentTrace
