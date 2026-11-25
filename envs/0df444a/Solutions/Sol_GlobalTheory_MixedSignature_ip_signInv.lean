-- Prove2me | solution 1 for GlobalTheory.MixedSignature.ip_signInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:19.057317+00:00
-- url     : https://prove2.me/submissions/1774d06a-e384-4911-b5e7-9768881f9669

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
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
theorem _root_.solution {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (v q : Fin r → E) :
    ip X (Ly X y (X.embV v)) (signInv X p (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm G v q)).re := by
  simp only [ip]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [← hermC_emb, hermC_normal (hy τ).1 _ (hy τ).2]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [signInv, Ly, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Complex.conj_ofReal, Data.embV]
  ring
end GlobalTheory.MixedSignature
