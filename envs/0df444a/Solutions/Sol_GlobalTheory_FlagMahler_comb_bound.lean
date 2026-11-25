-- Prove2me | solution 1 for GlobalTheory.FlagMahler.comb_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:39.494809+00:00
-- url     : https://prove2.me/submissions/bb70a10e-40f1-46f0-9166-0f3443428078

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
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
open Complex
open NumberField Module
open Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
open Complex
namespace GlobalTheory.FlagMahler
namespace _root_.GlobalTheory.FlagMahler
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ)
    {ι : Type} [Fintype ι] (q : ι → ℚ) (f : ι → Fin r → E) (b : Fin r) :
    ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (∑ i, q i • f i)) b‖ ≤
      ∑ i, ‖(q i : ℂ)‖ * (1 + _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (f i) / X.c τ) := by
  have he : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (∑ i, q i • f i) = ∑ i, (q i : ℂ) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (f i) := by
    ext a
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Finset.sum_apply, map_sum, Rat.smul_def]
  rw [he, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ
  have h := _root_.GlobalTheory.FlagMahler.comp_le_Qy X y τ (f i) b
  have h2 : ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (f i)) b‖ ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (f i) / X.c τ := by
    rw [le_div_iff₀ hc]; linarith
  nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (f i)) b‖ - 1)]
end _root_.GlobalTheory.FlagMahler
end GlobalTheory.FlagMahler
