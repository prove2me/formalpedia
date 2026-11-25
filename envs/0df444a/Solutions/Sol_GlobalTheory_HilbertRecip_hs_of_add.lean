-- Prove2me | solution 1 for GlobalTheory.HilbertRecip.hs_of_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:08.357685+00:00
-- url     : https://prove2.me/submissions/42509fb3-c64c-4f52-a9da-52b345ebb3ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitMemGlobalNormOfMemLocalNorms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_eq_one_iff
import Theorems.Thm_GlobalTheory_HilbertRecip_mem_nrm_of_sqr
import Theorems.Thm_GlobalTheory_HilbertRecip_sq_mem_sqr
import Theorems.Thm_GlobalTheory_HilbertRecip_mem_nrm_of_eq
import Theorems.Thm_GlobalTheory_HilbertRecip_neg_mem_nrm
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_comm
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_mul_right
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


section
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
namespace GlobalTheory.HilbertRecip
variable {F : Type} [Field F] [NumberField F]
private lemma hs_mul_sq_right (q : Place F) (a b c : Fˣ) : hs q a (b * c ^ 2) = hs q a b := by
  rw [hs_mul_right, hs_eq_one_iff.mpr (mem_nrm_of_sqr (sq_mem_sqr q c) a), mul_one]
end GlobalTheory.HilbertRecip
namespace GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
end GlobalTheory.QuadSymbol
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.HilbertRecip
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbertRecip
theorem _root_.solution (q : Place F) {α β γ : Fˣ} (h : (α : F) + β = γ) :
    hs q α β = hs q (-(α * β)) γ := by
  have hinv : ∀ x : Fˣ, hs q x γ⁻¹ = hs q x γ := by
    intro x
    have e : γ⁻¹ = γ * γ⁻¹ ^ 2 := by group
    rw [e, hs_mul_sq_right]
  have h1 : hs q (α * γ⁻¹) (β * γ⁻¹) = 1 := by
    rw [hs_eq_one_iff]
    apply mem_nrm_of_eq q (x := 1) (y := 1)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, one_pow, mul_one]
    rw [eq_sub_iff_add_eq, ← add_mul, h, mul_inv_cancel₀ γ.ne_zero]
  have e1 : hs q (α * γ⁻¹) (β * γ⁻¹) = hs q α β * hs q α γ * (hs q β γ * hs q γ γ) := by
    rw [hs_mul_left q α γ⁻¹, hs_mul_right q α β γ⁻¹, hinv α, hs_comm q γ⁻¹ (β * γ⁻¹),
      hinv (β * γ⁻¹), hs_mul_left q β γ⁻¹ γ, hs_comm q γ⁻¹ γ, hinv γ]
  have e2 : hs q (-(α * β)) γ = hs q (-1) γ * hs q α γ * hs q β γ := by
    have e : -(α * β) = -1 * α * β := by rw [mul_assoc, neg_one_mul]
    rw [e, hs_mul_left, hs_mul_left]
  have e3 : hs q (-1) γ * hs q γ γ = 1 := by
    rw [← hs_mul_left, neg_one_mul]
    exact hs_eq_one_iff.mpr (neg_mem_nrm q γ)
  rw [e2]
  rw [e1] at h1
  rcases Int.units_eq_one_or (hs q α β) with hA | hA <;>
  rcases Int.units_eq_one_or (hs q α γ) with hB | hB <;>
  rcases Int.units_eq_one_or (hs q β γ) with hC | hC <;>
  rcases Int.units_eq_one_or (hs q γ γ) with hD | hD <;>
  rcases Int.units_eq_one_or (hs q (-1) γ) with hE | hE <;>
  rw [hA, hB, hC, hD] at h1 <;> rw [hD, hE] at e3 <;> rw [hA, hB, hC, hE] <;>
  revert h1 e3 <;> decide
end GlobalTheory.HilbertRecip
