-- Prove2me | solution 1 for GlobalTheory.FlagMahler.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:59.416899+00:00
-- url     : https://prove2.me/submissions/c607adbe-9e97-43ca-bb8b-452f6c9c5c2a

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_hermC_normal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj
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
namespace GlobalTheory.FlagMahler
theorem _root_.solution {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set Gt := X.Gm.map τ with hGtdef
  have hGt : Gt.det ≠ 0 := by
    have e : (X.Gm.map τ).det = τ X.Gm.det := by rw [RingHom.map_det]; rfl
    rw [hGtdef, e]; exact (map_ne_zero τ).mpr X.Gm_det
  have hGG : Gt * Gt⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGt)
  set q : Fin r → ℂ := fun k => conj (Gt⁻¹ k l) with hq
  have h1 : hermC τ X.Gm (col Y b) q = Y l b := by
    have e : ∀ a, ∑ c, Y a b * τ (X.Gm a c) * conj (q c) = Y a b * (Gt * Gt⁻¹) a l := by
      intro a
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hq, Complex.conj_conj, hGtdef, Matrix.map_apply]
      ring
    simp only [hermC, col]
    simp_rw [e, hGG, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have h2 := IntegralBasisReduction.hermC_normal X hY _ hg (col Y b) q
  have h3 : Y⁻¹ *ᵥ col Y b = Pi.single b 1 := by
    have : col Y b = Y *ᵥ Pi.single b 1 := by funext i; simp [col]
    rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hY), one_mulVec]
  rw [h3] at h2
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  rw [← h1, h2, norm_mul, Complex.norm_conj]
  have hs : ‖(((sgn X.p0 (b : ℕ) : ℝ) : ℂ))‖ = 1 := by
    unfold sgn; split_ifs <;> simp
  rw [hs, one_mul]
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, hq, Complex.norm_conj, mul_comm]
end GlobalTheory.FlagMahler
