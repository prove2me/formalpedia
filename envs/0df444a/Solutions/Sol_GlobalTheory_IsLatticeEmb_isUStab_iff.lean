-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.isUStab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:29.32897+00:00
-- url     : https://prove2.me/submissions/528884de-3a26-441e-91b7-abb55943bef2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
import Theorems.Thm_GlobalTheory_herm_mulVec
import Theorems.Thm_GlobalTheory_EFf_mulVec_iff
import Theorems.Thm_GlobalTheory_IsLatticeEmb_bilin_ext
import Theorems.Thm_GlobalTheory_IsLatticeEmb_comp_GL
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
theorem _root_.solution (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) (γ : GL (Fin r) E) :
    IsUStab G (LinearMap.range φ) γ ↔
      ∃ g : M ≃ₗ[𝓞 E] M, (∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ x = φ (g x)) ∧
        ∀ x y, β (g x) (g y) = β x y := by
  have hinj : Function.Injective (γ : Matrix (Fin r) (Fin r) E).mulVec :=
    mulVec_injective_iff_isUnit.mpr γ.isUnit
  constructor
  · rintro ⟨hu, hs⟩
    have h2 := h.comp_GL γ
    have hr : LinearMap.range (((γ : Matrix (Fin r) (Fin r) E).mulVecLin.restrictScalars (𝓞 E)) ∘ₗ φ)
        = LinearMap.range φ := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact (hs _).mp ⟨x, rfl⟩
      · intro hv
        obtain ⟨w, rfl⟩ := mulVec_surjective_iff_isUnit.mpr γ.isUnit v
        obtain ⟨x, rfl⟩ := (hs w).mpr hv
        exact ⟨x, rfl⟩
    let g : M ≃ₗ[𝓞 E] M := (LinearEquiv.ofInjective _ h2.1).trans
      ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective φ h.1).symm)
    have hg : ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ x = φ (g x) := fun x => by
      simp only [g, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
      rfl
    refine ⟨g, hg, fun x y => ?_⟩
    have : ((β (g x) (g y) : ℤ) : ℚ) = β x y := by rw [← hG, ← hG, ← hg, ← hg, EFf, EFf, hu]
    exact_mod_cast this
  · rintro ⟨g, hg, hβ⟩
    refine ⟨(EFf_mulVec_iff h0 G G _).mp fun v w => ?_, fun v => ⟨?_, ?_⟩⟩
    · have : traceFormBilin ξ0 ((γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc)
          = traceFormBilin ξ0 G := h.bilin_ext fun x y => by
        rw [traceFormBilin_apply, traceFormBilin_apply, EFf, ← herm_mulVec, hg, hg, ← EFf, hG, hG, hβ]
      rw [EFf, herm_mulVec, ← EFf, ← traceFormBilin_apply, this, traceFormBilin_apply]
    · rintro ⟨x, rfl⟩
      exact ⟨g x, (hg x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨g.symm x, hinj ?_⟩
      rw [hg, g.apply_symm_apply, hx]
end GlobalTheory.IsLatticeEmb
