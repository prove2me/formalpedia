-- Prove2me | solution 1 for GlobalTheory.datum_gram_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:41.547864+00:00
-- url     : https://prove2.me/submissions/ca5aa2e8-edad-4041-9e00-3c9f82c76f9f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_GlobalTheory_IsLatticeEmb_EFf_gram
import Theorems.Thm_GlobalTheory_IsLatticeEmb_gram_herm
import Theorems.Thm_GlobalTheory_IsLatticeEmb_gram_det_ne_zero_iff
import Theorems.Thm_GlobalTheory_IsLatticeEmb_EF_int_of_eq
import Theorems.Thm_GlobalTheory_IsLatticeEmb_EF_perf_iff
import Theorems.Thm_GlobalTheory_datum_isIntConjAdj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.FD hiding cc_cc cc_sub cc_mul cc_one cc_zero cc_eq_zero
open ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {H : Host E}
namespace GlobalTheory
theorem _root_.solution (D : Datum H) {φ : D.La →ₗ[𝓞 E] (Fin r → E)} (h : IsLatticeEmb φ)
    {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    (∀ a b, cc (h.gram ξ0 D.EF a b) = h.gram ξ0 D.EF b a) ∧ (h.gram ξ0 D.EF).det ≠ 0 ∧
      (∀ x y, EFf ξ0 (h.gram ξ0 D.EF) (φ x) (φ y) = D.EF x y) ∧
      (∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
        ∃ k : ℤ, EFf ξ0 (h.gram ξ0 D.EF) x y = k) ∧
      ∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
        (f y : ℚ) = EFf ξ0 (h.gram ξ0 D.EF) x y :=
  have hβ := datum_isIntConjAdj D
  ⟨h.gram_herm h0 hξ hβ D.alt, (h.gram_det_ne_zero_iff h0 hβ).mpr D.unimod.1, h.EFf_gram h0 hβ,
    IsLatticeEmb.EF_int_of_eq (h.EFf_gram h0 hβ),
    (h.EF_perf_iff (h.EFf_gram h0 hβ)).mpr D.unimod.2⟩
end GlobalTheory
