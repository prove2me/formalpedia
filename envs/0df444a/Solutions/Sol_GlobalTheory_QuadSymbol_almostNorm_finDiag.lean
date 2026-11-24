-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.almostNorm_finDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:41.789815+00:00
-- url     : https://prove2.me/submissions/4c18d935-225e-4c98-87c8-1a4e924e1eae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Theorems.Thm_GlobalTheory_QuadSymbol_AlmostNorm_exists_basis_sq
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_exists_integral_sq_sub_mul_sq_of_unit
import Theorems.Thm_GlobalTheory_QNorm_finite_valuation_ne_one
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff_form
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
open GlobalTheory GlobalTheory.QuadSymbol
namespace GlobalTheory.QuadSymbol
theorem _root_.solution :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ t : Kˣ, AlmostNorm K L (finDiag K t) := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine (((GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ0))).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K t)).subset ?_
  intro v hv
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Units.val_mk0] at hn
  obtain ⟨⟨h2, hd⟩, ht⟩ := hn
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  obtain ⟨x, -, y, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v
    (algebraMap K _ δ) (algebraMap K _ (t : K))
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2) (by rw [key, hd]) (by rw [key, ht])
  exact hv ((mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩)
end GlobalTheory.QuadSymbol
