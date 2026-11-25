-- Prove2me | solution 1 for GlobalTheory.MixedSignature.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:28.965001+00:00
-- url     : https://prove2.me/submissions/90755490-9761-49c8-b350-53cf1b2952d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
import Theorems.Thm_GlobalTheory_MixedSignature_hermC_normal
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_col_map_eq
import Theorems.Thm_GlobalTheory_FlagMahler_comb_bound
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq
import Theorems.Thm_GlobalTheory_FlagMahler_inv_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_phi
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Am_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ipB_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
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
open GlobalTheory GlobalTheory.MixedSignature
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module Complex
open Matrix hiding col gram
open scoped ComplexConjugate
open QuadraticLatticeForms (ip ipB ipB_apply Ly Am Qy Ly_injective Ly_surjective quad_int Am_posDef)
open HermitianLatticeMaps (phi phi_f phi_zsum phi_mem phi_phi smul_coe coe_expand mulQ mulQ_apply)
open GlobalTheory.FlagMahler (col_map_eq inv_lact comp_le_Qy comb_bound Qy_smul_le finite_int_sq)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ}
namespace GlobalTheory.MixedSignature
theorem _root_.solution (hG : G.det ≠ 0) {q0 : ℕ} {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ G Y = diagonal fun a : Fin r => ((sgn q0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(G.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set Gt := G.map τ with hGtdef
  have hGt : Gt.det ≠ 0 := by
    have e : (G.map τ).det = τ G.det := by rw [RingHom.map_det]; rfl
    rw [hGtdef, e]; exact (map_ne_zero τ).mpr hG
  have hGG : Gt * Gt⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGt)
  set q : Fin r → ℂ := fun k => conj (Gt⁻¹ k l) with hq
  have h1 : hermC τ G (col Y b) q = Y l b := by
    have e : ∀ a, ∑ c, Y a b * τ (G a c) * conj (q c) = Y a b * (Gt * Gt⁻¹) a l := by
      intro a
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hq, Complex.conj_conj, hGtdef, Matrix.map_apply]
      ring
    simp only [hermC, col]
    simp_rw [e, hGG, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have h2 := hermC_normal hY _ hg (col Y b) q
  have h3 : Y⁻¹ *ᵥ col Y b = Pi.single b 1 := by
    have : col Y b = Y *ᵥ Pi.single b 1 := by funext i; simp [col]
    rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hY), one_mulVec]
  rw [h3] at h2
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  rw [← h1, h2, norm_mul, Complex.norm_conj]
  have hs : ‖(((sgn q0 (b : ℕ) : ℝ) : ℂ))‖ = 1 := by
    unfold sgn; split_ifs <;> simp
  rw [hs, one_mul]
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, hq, Complex.norm_conj, mul_comm]
end GlobalTheory.MixedSignature
