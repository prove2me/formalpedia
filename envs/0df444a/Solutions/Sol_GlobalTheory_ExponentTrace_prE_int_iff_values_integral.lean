-- Prove2me | solution 1 for GlobalTheory.ExponentTrace.prE_int_iff_values_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:17.100155+00:00
-- url     : https://prove2.me/submissions/fe72a866-296d-42a0-bd7b-6cc1d655b656

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
import Theorems.Thm_GlobalTheory_ExponentTrace_mem_one_iff_range
import Theorems.Thm_GlobalTheory_ExponentTrace_coord_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_conj_mem_pairIdeal
import Theorems.Thm_GlobalTheory_ExponentTrace_entry_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_pair_iff
import Theorems.Thm_GlobalTheory_ExponentTrace_skew_iff
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
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
namespace GlobalTheory.ExponentTrace
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (χ : Matrix (Fin ρ) (Fin ρ) E), 0 < N → (∀ b, cc' b ≠ 0) → FJ.IsHermE χ → ((∀ β, FJ.IsSkew β → (∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z) → ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u m : Fin ρ → E, (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → m a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ H r ρ X N cc' χ hN hc hχ
  have h1 := skew_iff H X (fun a b => pairIdeal N (cc' a) (cc' b))
    (fun a b s hs => conj_mem_pairIdeal hs) χ hχ
  simp only [entry_iff N _ (hc _), coord_iff (hc _)]
  rw [h1]
  simp only [pair_iff hN (hc _) (hc _), mem_one_iff_range]
  constructor
  · intro h u m hu hm
    simp only [Finset.mul_sum]
    exact Submodule.sum_mem ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) fun i _ =>
      Submodule.sum_mem _ fun k _ => h i k _ (hu i) _ (hm k)
  · intro h a b u hu m hm
    have hc0 : cc (0 : E) = 0 := map_zero _
    have hs : ∀ (a : Fin ρ) (u : E), u ∈ dif E * cc' a →
        ∀ i, (Pi.single a u : Fin ρ → E) i ∈ dif E * cc' i := fun a u hu i => by
      by_cases hi : i = a
      · subst hi; simpa using hu
      · rw [Pi.single_eq_of_ne hi]; exact FractionalIdeal.zero_mem _
    have := h _ _ (hs a u hu) (hs b m hm)
    simpa [Pi.single_apply, apply_ite cc, hc0] using this
end GlobalTheory.ExponentTrace
