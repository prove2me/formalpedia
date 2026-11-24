-- Prove2me | solution 1 for GlobalTheory.QuadraticValuationIndexTwo.exists_mul_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:06.800574+00:00
-- url     : https://prove2.me/submissions/6a67edb2-72f3-458a-b7a3-7200722343b7

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Theorems.Thm_GlobalTheory_CNorm_kummer_basic
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
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
open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex
open GlobalTheory GlobalTheory.QuadraticValuationIndexTwo
namespace GlobalTheory.QuadraticValuationIndexTwo
theorem _root_.solution {B E : Type} [Field B] [CharZero B] [Field E] [Algebra B E] {d : B}
    {θ : E} {σ : E ≃ₐ[B] E} (h : IsKum 2 (-1 : B) d θ σ) (x : B) :
    (∃ y : E, y * σ y = algebraMap B E x) ↔ Nm d x := by
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ h
  have hinv : ∀ z, σ (σ z) = z := fun z => kb.2.2.1 z
  have hfix := kb.2.2.2.1
  have hpow : θ ^ 2 = algebraMap B E d := h.pow
  have hconj : σ θ = -θ := by rw [h.conj, map_neg, map_one, neg_one_mul]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap B E).injective
  have hθ : θ ≠ 0 := by
    intro h0
    apply h.nonpow 0
    apply (algebraMap B E).injective
    rw [← hpow, h0]
    simp
  constructor
  · rintro ⟨y, hy⟩

    obtain ⟨a, ha⟩ := hfix ((y + σ y) / 2) (by
      rw [map_div₀, map_add, hinv, map_ofNat, add_comm])
    obtain ⟨b, hb⟩ := hfix ((y - σ y) / (2 * θ)) (by
      rw [map_div₀, map_sub, hinv, map_mul, hconj, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub])
    have hy' : y = algebraMap B E a + algebraMap B E b * θ := by
      rw [← ha, ← hb]
      field_simp
      ring
    have hσy : σ y = algebraMap B E a - algebraMap B E b * θ := by
      rw [hy', map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
      ring
    refine ⟨a, b, (algebraMap B E).injective ?_⟩
    rw [← hy, hσy, hy']
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring
  · rintro ⟨a, b, rfl⟩
    refine ⟨algebraMap B E a + algebraMap B E b * θ, ?_⟩
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring
end GlobalTheory.QuadraticValuationIndexTwo
