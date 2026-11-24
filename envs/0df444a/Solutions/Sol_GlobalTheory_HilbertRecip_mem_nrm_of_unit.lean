-- Prove2me | solution 1 for GlobalTheory.HilbertRecip.mem_nrm_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:18:23.271801+00:00
-- url     : https://prove2.me/submissions/6c2f968a-a27f-4c64-8925-eadadf78618d

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
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_Defect_evenNorms_of_le_four
import Theorems.Thm_GlobalTheory_QNorm_Defect_exists_exp
import Theorems.Thm_GlobalTheory_QNorm_hiUnits_le_sqs_hiUnits
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_isSquare_left
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_sq
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_nm_mul_adicCompletion
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
private lemma not_nm_of_valuation_eq_exp_neg_one {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {B z : K}
    (hE : EvenNorms w B) (hz : w z = WithZero.exp (-1)) : ¬ Nm B z := by
  rintro ⟨x, y, rfl⟩
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at hz
    have h0 : w ((0 : K) ^ 2 - B * 0 ^ 2) = 0 := by simp
    rw [h0] at hz
    exact WithZero.exp_ne_zero hz.symm
  obtain ⟨n, hn⟩ := hE x y hne
  rw [hn, WithZero.exp_inj] at hz
  omega
private lemma isSquare_of_valued_sub_one_lt_four {v : HeightOneSpectrum (𝓞 F)}
    (h2 : Valued.v (2 : v.adicCompletion F) = 1) (x : v.adicCompletion F)
    (hx : Valued.v (x - 1) < Valued.v (4 : v.adicCompletion F)) : IsSquare x := by
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  rw [h4] at hx
  by_cases hx1 : x - 1 = 0
  · rw [sub_eq_zero.1 hx1]
    exact ⟨1, by simp⟩
  obtain ⟨n, hn⟩ := Defect.exists_exp Valued.v hx1
  have hxv : Valued.v x = 1 := by
    have hsplit : x = (x - 1) + 1 := by ring
    rw [hsplit, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
    exact map_one _
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxv
    exact zero_ne_one hxv
  have hle : Valued.v (x - 1) ≤ WithZero.exp (-(((2 * 0 + 1 : ℕ)) : ℤ)) := by
    rw [hn] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    push_cast
    omega
  have hmem : Units.mk0 x hx0 ∈
      hiUnits (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (2 * 0 + 1) :=
    ⟨hxv, hle⟩
  obtain ⟨y, -, hy⟩ := hiUnits_le_sqs_hiUnits F v 0 (by rw [h2]; simp) hmem
  refine ⟨(y : v.adicCompletion F), ?_⟩
  have hyx := congrArg Units.val hy
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] at hyx
  rw [← hyx, sq]
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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {a b : Fˣ} (h2 : v.valuation F 2 = 1)
    (ha : v.valuation F (a : F) = 1) (hb : v.valuation F (b : F) = 1) : a ∈ nrm (.inl v) b := by
  set K := v.adicCompletion F
  have hval : ∀ x : F, (Valued.v (algebraMap F K x) : WithZero (Multiplicative ℤ)) = v.valuation F x := fun x =>
    v.valuedAdicCompletion_eq_valuation' x
  show ∃ x y : K, algebraMap F K (a : F) = x ^ 2 - algebraMap F K (b : F) * y ^ 2
  have h2' : Valued.v (2 : K) = 1 := by
    have := hval 2
    rw [map_ofNat] at this
    rw [this, h2]
  have hK2 : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2'
    exact zero_ne_one h2'
  have hA0 : algebraMap F K (a : F) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hB0 : algebraMap F K (b : F) ≠ 0 := (map_ne_zero _).2 b.ne_zero
  by_cases hsq : IsSquare (algebraMap F K (b : F))
  · exact Nm.of_isSquare_left hK2 hB0 hsq _
  · have hB1 : Valued.v (algebraMap F K (b : F)) = 1 := by rw [hval, hb]
    have h4 : Valued.v (4 : K) = 1 := by
      rw [show (4 : K) = 2 * 2 by norm_num, map_mul, h2', one_mul]
    have hle : Valued.v (algebraMap F K (b : F) - 1) ≤ Valued.v (4 : K) := by
      rw [h4]
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [hB1, map_one, max_self]
    have hE := Defect.evenNorms_of_le_four Valued.v hK2 (isSquare_of_valued_sub_one_lt_four h2') _ hB1 hsq hle
    by_contra hA
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hP : Valued.v (algebraMap F K π) = WithZero.exp (-1) := by rw [hval, hπ]
    have hP0 : algebraMap F K π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hP
      exact WithZero.exp_ne_zero hP.symm
    have hPn := not_nm_of_valuation_eq_exp_neg_one _ hE hP
    have hprod := nm_mul_adicCompletion F v hB0 hA0 hP0 hA hPn
    refine not_nm_of_valuation_eq_exp_neg_one _ hE ?_ hprod
    rw [map_mul, hval, ha, one_mul, hP]
end GlobalTheory.HilbertRecip
