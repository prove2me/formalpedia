-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.gram_eq_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:10.905067+00:00
-- url     : https://prove2.me/submissions/e2d697cb-fa68-4125-8d31-a7b747325e92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_GlobalTheory_herm_mulVec
import Theorems.Thm_GlobalTheory_IsLatticeEmb_EFf_gram
import Theorems.Thm_GlobalTheory_IsLatticeEmb_eq_gram
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
open GlobalTheory.IsLatticeEmb
variable {φ : M →ₗ[𝓞 E] (Fin r → E)}
namespace GlobalTheory.IsLatticeEmb
theorem _root_.solution {s : ℕ} {φ' : M' →ₗ[𝓞 E] (Fin s → E)} (h : IsLatticeEmb φ)
    (h' : IsLatticeEmb φ') {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {β' : LinearMap.BilinForm ℤ M'} (hβ' : IsIntConjAdj E β') {g : M → M'}
    (hg : ∀ x y, β' (g x) (g y) = β x y) {γ : Matrix (Fin s) (Fin r) E}
    (hγ : ∀ x, γ *ᵥ φ x = φ' (g x)) : h.gram ξ0 β = γᵀ * h'.gram ξ0 β' * γ.map cc := by
  refine (h.eq_gram h0 fun x y => ?_).symm
  rw [← hg, ← h'.EFf_gram h0 hβ', ← hγ, ← hγ, EFf, EFf, herm_mulVec]
end GlobalTheory.IsLatticeEmb
