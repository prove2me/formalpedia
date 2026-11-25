-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.extend_isConjAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:14.112905+00:00
-- url     : https://prove2.me/submissions/f393206e-b96e-4025-84fd-e42a3476b054

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_GlobalTheory_coe_ringOfIntegersComplexConj
import Theorems.Thm_GlobalTheory_IsLatticeEmb_extend_apply
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IsLatticeEmb.extend_apply
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
theorem _root_.solution (h : IsLatticeEmb φ) {β : LinearMap.BilinForm ℤ M}
    (hβ : IsIntConjAdj E β) : IsConjAdj (h.extend β) := by
  intro a v w
  obtain ⟨m, hm, x, hx⟩ := h.exists_zsmul v
  obtain ⟨n, hn, y, hy⟩ := h.exists_zsmul w
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hint⟩ := halg.exists_integral_multiple
  let α : 𝓞 E := ⟨k • a, hint⟩
  have hα : (α : E) = k • a := rfl
  have h1 : φ (α • x) = k • m • a • v := by
    rw [map_smul, ← algebraMap_smul E α, hx, smul_comm m a v, ← smul_assoc k]; rfl
  have h2 : φ (IsCMField.ringOfIntegersComplexConj E α • y) = k • n • cc a • w := by
    rw [map_smul, ← algebraMap_smul E (IsCMField.ringOfIntegersComplexConj E α), hy,
      smul_comm n (cc a) w, ← smul_assoc k]
    congr 1
    change ((IsCMField.ringOfIntegersComplexConj E α : 𝓞 E) : E) = _
    rw [coe_ringOfIntegersComplexConj, hα, zsmul_eq_mul, zsmul_eq_mul, cc_mul, cc_intCast]
  have h3 : h.extend β (φ (α • x)) (φ y) =
      h.extend β (φ x) (φ (IsCMField.ringOfIntegersComplexConj E α • y)) := by
    rw [extend_apply, extend_apply, hβ]
  simp only [h1, h2, hx, hy, map_zsmul, LinearMap.smul_apply] at h3
  rw [smul_comm k n] at h3
  exact smul_right_injective ℚ hm (smul_right_injective ℚ hk (smul_right_injective ℚ hn h3))
end GlobalTheory.IsLatticeEmb
