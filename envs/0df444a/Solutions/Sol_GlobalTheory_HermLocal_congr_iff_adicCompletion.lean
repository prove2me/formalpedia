-- Prove2me | solution 1 for GlobalTheory.HermLocal.congr_iff_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:38.101928+00:00
-- url     : https://prove2.me/submissions/2ded7fa3-5f4f-473a-9a71-46170160d12a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_HermLocal_congr_iff_of_five
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_adicCompletion_of_five_le
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
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
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
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal
namespace GlobalTheory.HermLocal
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type*) [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L] (σ : L ≃ₐ[v.adicCompletion F] L)
    (hσ : σ ≠ 1) {r : ℕ} {G G' : Matrix (Fin r) (Fin r) L} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      ∃ x : L, G.det / G'.det = x * σ x := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  exact congr_iff_of_five two_ne_zero (isotropic_adicCompletion_of_five_le F v (by simp)) σ hσ
    hG hG' hd hd'
end GlobalTheory.HermLocal
