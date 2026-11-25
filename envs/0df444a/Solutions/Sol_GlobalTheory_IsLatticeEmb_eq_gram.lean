-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.eq_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:20.026156+00:00
-- url     : https://prove2.me/submissions/44618e6b-28e0-47fd-8a3f-842e2b20b3e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_GlobalTheory_IsLatticeEmb_bilin_ext
import Theorems.Thm_GlobalTheory_IsLatticeEmb_extend_apply
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
attribute [local simp] GlobalTheory.IsLatticeEmb.extend_apply
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
theorem _root_.solution (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    G = h.gram ξ0 β := by
  have : h.extend β = traceFormBilin ξ0 G := h.bilin_ext fun x y => by rw [extend_apply, traceFormBilin_apply, hG]
  rw [gram, this, skewGram_traceFormBilin h0]
end GlobalTheory.IsLatticeEmb
