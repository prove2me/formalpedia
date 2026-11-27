-- Prove2me | solution 1 for GlobalTheory.latticeEF_bijective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:19.187209+00:00
-- url     : https://prove2.me/submissions/991d4dac-b777-4e34-abf2-5a84a9fe1cf8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_GlobalTheory_IsLatticeEmb_gram_det_ne_zero_iff
import Theorems.Thm_GlobalTheory_IsLatticeEmb_EF_perf_iff
import Theorems.Thm_GlobalTheory_latticeEF_apply
import Theorems.Thm_GlobalTheory_latticeEF_isIntConjAdj
import Theorems.Thm_GlobalTheory_gram_latticeEF
import Theorems.Thm_GlobalTheory_isLatticeEmb_subtype
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
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup M'] [Module (𝓞 E) M']
variable {ξ0 : E} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
  (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k)
namespace GlobalTheory
theorem _root_.solution (hΛ : IsLattice Λ) (h0 : ξ0 ≠ 0) :
    Function.Bijective (latticeEF ξ0 G Λ hint) ↔
      G.det ≠ 0 ∧ ∀ f : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (f y : ℚ) = EFf ξ0 G x y := by
  have h := isLatticeEmb_subtype hΛ
  have h1 := h.gram_det_ne_zero_iff h0 (latticeEF_isIntConjAdj hint)
  rw [gram_latticeEF hint hΛ h0] at h1
  have h2 := h.EF_perf_iff (ξ0 := ξ0) (G := G) fun x y => (latticeEF_apply hint x y).symm
  rw [Submodule.range_subtype] at h2
  rw [h1, h2]
  rfl
end GlobalTheory
