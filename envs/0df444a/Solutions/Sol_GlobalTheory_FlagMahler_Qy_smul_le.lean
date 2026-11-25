-- Prove2me | solution 1 for GlobalTheory.FlagMahler.Qy_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:05.803151+00:00
-- url     : https://prove2.me/submissions/7205a092-76e6-4aec-9096-9307fd400aea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos
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
open GlobalTheory GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open NumberField Module
open Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
namespace GlobalTheory.FlagMahler
namespace _root_.GlobalTheory.FlagMahler
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (α • v) ≤ (∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have he : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (α • v) = (τ.1 α) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v := by
    ext a
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  rw [he, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum]
  have h1 : ‖τ.1 α‖ ^ 2 ≤ ∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2 :=
    Finset.single_le_sum (f := fun σ : X.Ψ => ‖σ.1 α‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ τ)
  have h2 : 0 ≤ ∑ a, ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) a‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 := (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ).le
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)]
end _root_.GlobalTheory.FlagMahler
end GlobalTheory.FlagMahler
