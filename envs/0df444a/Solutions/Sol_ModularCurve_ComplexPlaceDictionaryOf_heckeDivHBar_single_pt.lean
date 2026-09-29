-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/06ac9b00-9595-5397-b004-9a6007fc4aa0

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer
import Theorems.Thm_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Theorems.Thm_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open ModularForm
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf ComplexPlaceDictionaryOf coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData heckeAlphaHBar coe_heckeAlphaHBar HeckeBetaHDefined heckeBetaHBar coe_heckeBetaHBar HeckeAlphaHBarIntegral HeckeBetaHBarIntegral heckeDivHBar translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHTopFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset EvalSymm jqModC jqModC_rat map_jqModC ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le ComplexPlaceDictionaryOf.restrictAlong_pt_qExpand ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC ComplexPlaceDictionaryOf.exists_pt_eq_of_mem realizeOf_eq_div exists_modularPolynomialData_evalSymm jqModC_eq_qExpansion_E4_cube_div_discriminant exists_complexPlaceDictionaryOf jqModC_mem_intFormRatiosC xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap"
namespace GammaHConjGL
p2m_open "ModularCurve~mem_restrictAlong_iff"

variable (ℓ : ℕ)

def lowerConj (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, ℓ * γ 0 1; γ 1 0 / ℓ, γ 1 1], by
    have hdet := Matrix.det_fin_two γ.1
    rw [γ.2] at hdet
    have hdiv : (ℓ : ℤ) * (γ 1 0 / ℓ) = γ 1 0 := Int.mul_ediv_cancel' hγ
    rw [Matrix.det_fin_two_of]
    have : (γ 0 0 * γ 1 1 - ↑ℓ * γ 0 1 * (γ 1 0 / ↑ℓ) : ℤ) =
        γ 0 0 * γ 1 1 - γ 0 1 * (↑ℓ * (γ 1 0 / ↑ℓ)) := by ring
    rw [this, hdiv]
    linarith⟩

theorem lowerConj_apply_one_zero (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 1 0 = γ 1 0 / ℓ := rfl

theorem lowerConj_apply_zero_zero (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 0 0 = γ 0 0 := rfl

theorem lowerConj_apply_zero_one (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 0 1 = ℓ * γ 0 1 := rfl

theorem lowerConj_apply_one_one (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 1 1 = γ 1 1 := rfl

theorem heckeDiag_mul (hℓ : ℓ ≠ 0) (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    heckeDiagMatrix ℓ * (γ : GL (Fin 2) ℝ) =
      ((lowerConj ℓ γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeDiagMatrix ℓ := by
  obtain ⟨c, hc⟩ := hγ
  have h0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : ((lowerConj ℓ γ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 : ℤ) = c := by
    rw [lowerConj_apply_one_zero, hc, Int.mul_ediv_cancel_left _ h0]
  ext i j
  simp only [Units.val_mul, val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerConj_apply_zero_zero, lowerConj_apply_one_one,
      lowerConj_apply_zero_one, h10, hc, mul_comm]

end ModularCurve.GammaHConjGL

end

namespace CohCarrier p2m_export "CohCarrier" "mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 conjUpperMat conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjUpperMat_mem gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap" end CohCarrier
p2m_open_scoped "CohCarrier" in
open ModularCurve.GammaHConjGL in
open scoped MatrixGroups in

theorem CohCarrier.GammaH_inf_Gamma0_le_conjGL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
      CongruenceSubgroup.conjGL (CohCarrier.GammaH M H) (ModularForm.heckeDiagMatrix ℓ) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  rintro γ ⟨hγH, hγ0⟩
  have hγ' : ((M : ℤ) * ℓ) ∣ γ 1 0 := by
    have := (CongruenceSubgroup.Gamma0_mem).mp hγ0
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact_mod_cast h
  have hℓγ : (ℓ : ℤ) ∣ γ 1 0 := (dvd_mul_left _ _).trans hγ'
  obtain ⟨hγM, hγu⟩ := CohCarrier.mem_GammaH_iff.mp hγH
  have hδ0 : lowerConj ℓ γ hℓγ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem, lowerConj_apply_one_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨c, hc⟩ := hγ'
    rw [hc, show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring,
      Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ)]
    exact_mod_cast dvd_mul_right _ _
  refine CongruenceSubgroup.mem_conjGL.mpr ⟨lowerConj ℓ γ hℓγ, ?_, ?_⟩
  · refine CohCarrier.mem_GammaH_iff.mpr ⟨hδ0, ?_⟩
    have hu : CohCarrier.gamma0Units M ⟨lowerConj ℓ γ hℓγ, hδ0⟩ = CohCarrier.gamma0Units M ⟨γ, hγM⟩ := by
      ext
      rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
      rfl
    rw [hu]
    exact hγu
  · rw [eq_mul_inv_iff_mul_eq]
    exact (heckeDiag_mul ℓ hℓ γ hℓγ).symm

noncomputable section

p2m_open "UpperHalfPlane ModularCurve~mem_restrictAlong_iff P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.ModularCurve AlgebraicCurve Filter"
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf ComplexPlaceDictionaryOf coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData heckeAlphaHBar coe_heckeAlphaHBar HeckeBetaHDefined heckeBetaHBar coe_heckeBetaHBar HeckeAlphaHBarIntegral HeckeBetaHBarIntegral heckeDivHBar translation_mem_GammaH Gamma1_le_GammaH xHFunctionField xHTopFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset EvalSymm jqModC jqModC_rat map_jqModC ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le ComplexPlaceDictionaryOf.restrictAlong_pt_qExpand ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC ComplexPlaceDictionaryOf.exists_pt_eq_of_mem realizeOf_eq_div exists_modularPolynomialData_evalSymm jqModC_eq_qExpansion_E4_cube_div_discriminant exists_complexPlaceDictionaryOf jqModC_mem_intFormRatiosC xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap"
namespace HeckeDivHBarSinglePt
p2m_open "ModularCurve~mem_restrictAlong_iff"

section Counting

variable {G X : Type*} [Group G] [MulAction G X]

open MulAction in

theorem card_stabilizer_eq_card_filter_mul (H : Subgroup G) {ι : Type*} (R : ι → G)
    (s : Finset ι) (hcover : ∀ g : G, ∃ i ∈ s, g * (R i)⁻¹ ∈ H)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, R i * (R j)⁻¹ ∈ H → i = j) (y x : X) (g₀ : G)
    (hg₀ : g₀ • y = x) [DecidablePred fun i => R i • y ∈ orbit H x] :
    Nat.card (stabilizer G x) =
      (s.filter fun i => R i • y ∈ orbit H x).card * Nat.card (stabilizer H x) := by
  classical
  set T := s.filter fun i => R i • y ∈ orbit H x with hT
  have hidx : ∀ σ : stabilizer G x, ∃ i ∈ s, (σ : G) * g₀ * (R i)⁻¹ ∈ H := fun σ =>
    hcover ((σ : G) * g₀)
  choose idx hidx_mem hidx_H using hidx
  have hidx_unique : ∀ (σ : stabilizer G x) (i : ι), i ∈ s → (σ : G) * g₀ * (R i)⁻¹ ∈ H →
      i = idx σ := by
    intro σ i hi hH
    refine hdisj i hi (idx σ) (hidx_mem σ) ?_
    have : R i * (R (idx σ))⁻¹ = ((σ : G) * g₀ * (R i)⁻¹)⁻¹ * ((σ : G) * g₀ * (R (idx σ))⁻¹) := by
      group
    rw [this]
    exact H.mul_mem (H.inv_mem hH) (hidx_H σ)
  have hidx_T : ∀ σ : stabilizer G x, idx σ ∈ T := by
    intro σ
    rw [hT, Finset.mem_filter]
    refine ⟨hidx_mem σ, mem_orbit_iff.mpr ⟨⟨_, H.inv_mem (hidx_H σ)⟩, ?_⟩⟩
    rw [Subgroup.mk_smul, mul_inv_rev, mul_inv_rev, inv_inv, mul_smul, mul_smul,
      show (σ : G)⁻¹ • x = x from mem_stabilizer_iff.mp (inv_mem σ.2), ← hg₀, inv_smul_smul]
  have hbase : ∀ i ∈ T, ∃ σ : stabilizer G x, (σ : G) * g₀ * (R i)⁻¹ ∈ H := by
    intro i hi
    rw [hT, Finset.mem_filter] at hi
    obtain ⟨h, hh⟩ := mem_orbit_iff.mp hi.2
    refine ⟨⟨(h : G)⁻¹ * R i * g₀⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hg₀, inv_smul_smul, hg₀, ← hh,
        Subgroup.smul_def, inv_smul_smul]
    · rw [show (h : G)⁻¹ * R i * g₀⁻¹ * g₀ * (R i)⁻¹ = (h : G)⁻¹ by group]
      exact H.inv_mem h.2
  choose! base hbase_H using hbase
  have hquot : ∀ σ : stabilizer G x, (σ : G) * ((base (idx σ) : stabilizer G x) : G)⁻¹ ∈ H := by
    intro σ
    have h1 := hidx_H σ
    have h2 := hbase_H (idx σ) (hidx_T σ)
    have : (σ : G) * ((base (idx σ) : stabilizer G x) : G)⁻¹ =
        ((σ : G) * g₀ * (R (idx σ))⁻¹) * (((base (idx σ) : stabilizer G x) : G) * g₀ *
          (R (idx σ))⁻¹)⁻¹ := by group
    rw [this]
    exact H.mul_mem h1 (H.inv_mem h2)
  have hquot_stab : ∀ σ : stabilizer G x,
      (⟨_, hquot σ⟩ : H) ∈ stabilizer H x := by
    intro σ
    rw [mem_stabilizer_iff, Subgroup.mk_smul, mul_smul,
      show ((base (idx σ) : stabilizer G x) : G)⁻¹ • x = x from
        mem_stabilizer_iff.mp (inv_mem (base (idx σ)).2)]
    exact mem_stabilizer_iff.mp σ.2
  let F : stabilizer G x → T × stabilizer H x := fun σ =>
    ⟨⟨idx σ, hidx_T σ⟩, ⟨_, hquot_stab σ⟩⟩
  have hinv_stab : ∀ p : T × stabilizer H x,
      ((p.2 : H) : G) * ((base p.1 : stabilizer G x) : G) ∈ stabilizer G x := by
    intro p
    rw [mem_stabilizer_iff, mul_smul, mem_stabilizer_iff.mp (base (p.1 : ι)).2]
    have := mem_stabilizer_iff.mp p.2.2
    rwa [Subgroup.smul_def] at this
  let Finv : T × stabilizer H x → stabilizer G x := fun p => ⟨_, hinv_stab p⟩
  have hidx_Finv : ∀ p : T × stabilizer H x, idx (Finv p) = (p.1 : ι) := by
    rintro ⟨⟨i, hi⟩, e1⟩
    symm
    apply hidx_unique _ i (Finset.mem_filter.mp hi).1
    show ((e1 : H) : G) * ((base i : stabilizer G x) : G) * g₀ * (R i)⁻¹ ∈ H
    have : ((e1 : H) : G) * ((base i : stabilizer G x) : G) * g₀ * (R i)⁻¹ =
        ((e1 : H) : G) * (((base i : stabilizer G x) : G) * g₀ * (R i)⁻¹) := by group
    rw [this]
    exact H.mul_mem (e1 : H).2 (hbase_H i hi)
  let e : stabilizer G x ≃ T × stabilizer H x :=
    { toFun := F
      invFun := Finv
      left_inv := by
        intro σ
        apply Subtype.ext
        show ((σ : G) * ((base (idx σ) : stabilizer G x) : G)⁻¹) *
          ((base (idx σ) : stabilizer G x) : G) = σ
        group
      right_inv := by
        intro p
        have hi := hidx_Finv p
        apply Prod.ext
        · exact Subtype.ext hi
        · apply Subtype.ext; apply Subtype.ext
          show ((Finv p : stabilizer G x) : G) * ((base (idx (Finv p)) : stabilizer G x) : G)⁻¹
            = ((p.2 : H) : G)
          rw [hi]
          show ((p.2 : H) : G) * ((base p.1 : stabilizer G x) : G) *
            ((base (p.1 : ι) : stabilizer G x) : G)⁻¹ = ((p.2 : H) : G)
          group }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe]

end Counting

section Cosets

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Γ" => CohCarrier.GammaH M H
local notation "U" => CohCarrier.GammaHUpper M H ℓ

theorem hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
theorem hℓ0' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ0 ℓ

omit [NeZero M] in

theorem mem_GammaH_of_apply_11_eq_one {A : SL(2, ℤ)} (h0 : A ∈ CongruenceSubgroup.Gamma0 M) (h11 : ((A 1 1 : ℤ) : ZMod M) = 1) :
    A ∈ Γ := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := Units.ext (by rw [CohCarrier.val_gamma0Units]; exact h11)
  rw [this]; exact one_mem H

def Tpow (j : ℤ) : Γ :=
  ⟨ModularGroup.T ^ j, mem_GammaH_of_apply_11_eq_one M H
    (by rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T_zpow]; simp)
    (by rw [ModularGroup.coe_T_zpow]; simp)⟩

@[scoped simp] theorem coe_Tpow (j : ℤ) : ((Tpow M H j : Γ) : SL(2, ℤ)) = ModularGroup.T ^ j := rfl

theorem exists_bezout (h : ¬ ℓ ∣ M) : ∃ ab : ℤ × ℤ, (ℓ : ℤ) * ab.1 - ab.2 * M = 1 := by
  have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop)
  exact ⟨(u, -v), by linarith [huv, mul_comm u (ℓ : ℤ)]⟩

def bez : ℤ × ℤ :=
  if h : ¬ ℓ ∣ M then (exists_bezout M ℓ h).choose else (0, 0)

theorem bez_spec (h : ¬ ℓ ∣ M) : (ℓ : ℤ) * (bez M ℓ).1 - (bez M ℓ).2 * M = 1 := by
  rw [bez, dif_pos h]
  exact (exists_bezout M ℓ h).choose_spec

def gInfMat : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ℓ * (bez M ℓ).1, (bez M ℓ).2; M, 1]

theorem det_gInfMat (h : ¬ ℓ ∣ M) : (gInfMat M ℓ).det = 1 := by
  rw [gInfMat, Matrix.det_fin_two_of]
  linarith [bez_spec M ℓ h]

def gInf : Γ :=
  if h : ¬ ℓ ∣ M then
    ⟨⟨gInfMat M ℓ, det_gInfMat M ℓ h⟩, mem_GammaH_of_apply_11_eq_one M H
      (by rw [CongruenceSubgroup.Gamma0_mem]; simp [gInfMat]) (by simp [gInfMat])⟩
  else 1

theorem coe_gInf (h : ¬ ℓ ∣ M) :
    (((gInf M H ℓ : Γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = gInfMat M ℓ := by
  rw [gInf, dif_pos h]

def gPrimeMat : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(bez M ℓ).1, (bez M ℓ).2; M, ℓ]

theorem det_gPrimeMat (h : ¬ ℓ ∣ M) : (gPrimeMat M ℓ).det = 1 := by
  rw [gPrimeMat, Matrix.det_fin_two_of]
  linarith [bez_spec M ℓ h]

def gPrime : CongruenceSubgroup.Gamma0 M :=
  if h : ¬ ℓ ∣ M then
    ⟨⟨gPrimeMat M ℓ, det_gPrimeMat M ℓ h⟩, by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [gPrimeMat]⟩
  else 1

theorem coe_gPrime (h : ¬ ℓ ∣ M) :
    (((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      gPrimeMat M ℓ := by
  rw [gPrime, dif_pos h]

def rep : Option (Fin ℓ) → Γ
  | some j => Tpow M H (j : ℕ)
  | none => gInf M H ℓ

def idxSet : Finset (Option (Fin ℓ)) :=
  Finset.univ.filter fun i => i.isSome ∨ ¬ ℓ ∣ M

omit [NeZero M] [Fact ℓ.Prime] in
@[scoped simp] theorem some_mem_idxSet (j : Fin ℓ) : some j ∈ idxSet M ℓ := by
  simp [idxSet]

omit [NeZero M] [Fact ℓ.Prime] in
@[scoped simp] theorem none_mem_idxSet : none ∈ idxSet M ℓ ↔ ¬ ℓ ∣ M := by
  simp [idxSet]

omit [NeZero M] [Fact ℓ.Prime] in
theorem mem_idxSet_iff (i : Option (Fin ℓ)) : i ∈ idxSet M ℓ ↔ (i.isSome ∨ ¬ ℓ ∣ M) := by
  simp [idxSet]

omit [NeZero M] in

theorem mem_upper_iff (γ : Γ) :
    γ ∈ U ↔ (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper]

omit [NeZero M] [Fact ℓ.Prime] in
theorem SL_mul_apply01 (A B : SL(2, ℤ)) :
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] [Fact ℓ.Prime] in
theorem SL_inv_apply (A : SL(2, ℤ)) :
    (A⁻¹) 0 0 = A 1 1 ∧ (A⁻¹) 0 1 = -A 0 1 ∧ (A⁻¹) 1 0 = -A 1 0 ∧ (A⁻¹) 1 1 = A 0 0 := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]

omit [NeZero M] [Fact ℓ.Prime] in
theorem T_zpow_apply (j : ℤ) :
    (ModularGroup.T ^ j) 0 0 = 1 ∧ (ModularGroup.T ^ j) 0 1 = j ∧ (ModularGroup.T ^ j) 1 0 = 0 ∧
      (ModularGroup.T ^ j) 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T_zpow]

theorem gInf_apply (h : ¬ ℓ ∣ M) :
    ((gInf M H ℓ : Γ) : SL(2, ℤ)) 0 0 = ℓ * (bez M ℓ).1 ∧
    ((gInf M H ℓ : Γ) : SL(2, ℤ)) 0 1 = (bez M ℓ).2 ∧
    ((gInf M H ℓ : Γ) : SL(2, ℤ)) 1 0 = M ∧
    ((gInf M H ℓ : Γ) : SL(2, ℤ)) 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · show (((gInf M H ℓ : Γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ _ = _
    rw [coe_gInf M H ℓ h]; simp [gInfMat]

theorem gPrime_apply (h : ¬ ℓ ∣ M) :
    ((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 0 0 = (bez M ℓ).1 ∧
    ((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 0 1 = (bez M ℓ).2 ∧
    ((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 1 0 = M ∧
    ((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 1 1 = ℓ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · show (((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ _ = _
    rw [coe_gPrime M ℓ h]; simp [gPrimeMat]

theorem gPrime_apply_11_mod (h : ¬ ℓ ∣ M) :
    ((((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
  rw [(gPrime_apply M ℓ h).2.2.2, Int.cast_natCast]

theorem not_dvd_apply00 (h : ℓ ∣ M) (γ : Γ) :
    (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) ≠ 0 := by
  intro h0
  have hdet := Matrix.det_fin_two (((γ : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Matrix.SpecialLinearGroup.det_coe] at hdet
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod ℓ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := CongruenceSubgroup.Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 H γ.2)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact (Int.natCast_dvd_natCast.mpr h).trans this
  have := congrArg (fun z : ℤ => (z : ZMod ℓ)) hdet
  simp only [Int.cast_one, Int.cast_sub, Int.cast_mul] at this
  rw [show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) = (γ : SL(2, ℤ)) 0 0 from rfl,
    show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) = (γ : SL(2, ℤ)) 1 0 from rfl,
    h0, h10] at this
  simp at this

theorem bez2_ne_zero (h : ¬ ℓ ∣ M) : (((bez M ℓ).2 : ℤ) : ZMod ℓ) ≠ 0 := by
  intro h0
  have := congrArg (fun z : ℤ => (z : ZMod ℓ)) (bez_spec M ℓ h)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, h0,
    Int.cast_one, zero_sub] at this
  simp at this

theorem cover (g : Γ) :
    ∃ i ∈ idxSet M ℓ, g * (rep M H ℓ i)⁻¹ ∈ U := by
  by_cases h00 : (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) = 0
  · have hN : ¬ ℓ ∣ M := fun hd => not_dvd_apply00 M H ℓ hd g h00
    refine ⟨none, (none_mem_idxSet M ℓ).mpr hN, ?_⟩
    rw [mem_upper_iff]
    simp only [rep, Subgroup.coe_mul, InvMemClass.coe_inv, SL_mul_apply01,
      (SL_inv_apply _).2.1, (SL_inv_apply _).2.2.2, (gInf_apply M H ℓ hN).1,
      (gInf_apply M H ℓ hN).2.1]
    push_cast
    rw [h00]; simp
  · obtain ⟨z, hz⟩ : ∃ z : ZMod ℓ, z * (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) =
        (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) := ⟨_ * (_)⁻¹, inv_mul_cancel_right₀ h00 _⟩
    refine ⟨some ⟨z.val, z.val_lt⟩, some_mem_idxSet M ℓ _, ?_⟩
    rw [mem_upper_iff]
    simp only [rep, Subgroup.coe_mul, InvMemClass.coe_inv, SL_mul_apply01, coe_Tpow,
      ← zpow_neg, (T_zpow_apply _).2.1, (T_zpow_apply _).2.2.2]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, ← hz]; ring

theorem disjoint (i : Option (Fin ℓ)) (hi : i ∈ idxSet M ℓ) (j : Option (Fin ℓ))
    (hj : j ∈ idxSet M ℓ) (hij : rep M H ℓ i * (rep M H ℓ j)⁻¹ ∈ U) :
    i = j := by
  rw [mem_upper_iff] at hij
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, SL_mul_apply01, (SL_inv_apply _).2.1,
    (SL_inv_apply _).2.2.2] at hij
  cases i with
  | none =>
    have hN := (none_mem_idxSet M ℓ).mp hi
    cases j with
    | none => rfl
    | some j =>
      exfalso
      simp only [rep, coe_Tpow, (T_zpow_apply _).1, (T_zpow_apply _).2.1,
        (gInf_apply M H ℓ hN).1, (gInf_apply M H ℓ hN).2.1] at hij
      push_cast at hij
      apply bez2_ne_zero M ℓ hN
      simpa using hij
  | some i =>
    cases j with
    | none =>
      have hN := (none_mem_idxSet M ℓ).mp hj
      exfalso
      simp only [rep, coe_Tpow, (T_zpow_apply _).1, (T_zpow_apply _).2.1,
        (gInf_apply M H ℓ hN).1, (gInf_apply M H ℓ hN).2.1] at hij
      push_cast at hij
      apply bez2_ne_zero M ℓ hN
      simpa using hij
    | some j =>
      simp only [rep, coe_Tpow, (T_zpow_apply _).1, (T_zpow_apply _).2.1] at hij
      push_cast at hij
      have : ((i : ℕ) : ZMod ℓ) = ((j : ℕ) : ZMod ℓ) := by linear_combination hij
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at this
      exact congrArg some (Fin.ext this)

end Cosets

section Up

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

local notation "Γ" => CohCarrier.GammaH M H
local notation "U" => CohCarrier.GammaHUpper M H ℓ
local notation "Γ'" => (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

theorem conjUpperMat_mem_top (h : U) :
    CohCarrier.conjUpperMat ℓ (h : SL(2, ℤ)) (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h) ∈ Γ' := by
  refine Subgroup.mem_inf.mpr ⟨CohCarrier.conjUpperMat_mem M H ℓ h, ?_⟩
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, CohCarrier.conjUpperMat_apply_10]
  have := CongruenceSubgroup.Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 H (h : Γ).2)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  push_cast
  exact mul_dvd_mul this dvd_rfl

def up (h : U) : ↥Γ' :=
  ⟨CohCarrier.conjUpperMat ℓ (h : SL(2, ℤ)) (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h), conjUpperMat_mem_top M H ℓ h⟩

@[scoped simp] theorem coe_up (h : U) :
    ((up M H ℓ h : ↥Γ') : SL(2, ℤ)) =
      CohCarrier.conjUpperMat ℓ (h : SL(2, ℤ)) (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h) := rfl

theorem conjUpperMat_apply (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (CohCarrier.conjUpperMat ℓ A h) 0 0 = A 0 0 ∧ (CohCarrier.conjUpperMat ℓ A h) 0 1 = A 0 1 / ℓ ∧
    (CohCarrier.conjUpperMat ℓ A h) 1 0 = A 1 0 * ℓ ∧ (CohCarrier.conjUpperMat ℓ A h) 1 1 = A 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [CohCarrier.conjUpperMat]

theorem up_bijective : Function.Bijective (up M H ℓ) := by
  have hℓ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  constructor
  · intro h₁ h₂ h12
    have h := congrArg (fun g : ↥Γ' => (g : SL(2, ℤ))) h12
    simp only [coe_up] at h
    apply Subtype.ext; apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hd₁ := CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h₁
    have hd₂ := CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h₂
    have e00 := congrArg (fun g : SL(2, ℤ) => g 0 0) h
    have e01 := congrArg (fun g : SL(2, ℤ) => g 0 1) h
    have e10 := congrArg (fun g : SL(2, ℤ) => g 1 0) h
    have e11 := congrArg (fun g : SL(2, ℤ) => g 1 1) h
    simp only [(conjUpperMat_apply ℓ _ _).1, (conjUpperMat_apply ℓ _ _).2.1, (conjUpperMat_apply ℓ _ _).2.2.1,
      (conjUpperMat_apply ℓ _ _).2.2.2] at e00 e01 e10 e11
    fin_cases i <;> fin_cases j
    · exact e00
    · have := congrArg (· * (ℓ : ℤ)) e01
      simp only [Int.ediv_mul_cancel hd₁, Int.ediv_mul_cancel hd₂] at this
      exact this
    · exact mul_right_cancel₀ hℓ e10
    · exact e11
  · rintro ⟨E, hE⟩
    obtain ⟨hEH, hE0⟩ := Subgroup.mem_inf.mp hE
    have hc : ((M : ℤ) * ℓ) ∣ E 1 0 := by
      have := CongruenceSubgroup.Gamma0_mem.mp hE0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact_mod_cast this
    have hℓc : (ℓ : ℤ) ∣ E 1 0 := (Dvd.intro_left _ rfl).trans hc
    let A : Matrix (Fin 2) (Fin 2) ℤ := !![E 0 0, E 0 1 * ℓ; E 1 0 / ℓ, E 1 1]
    have hdet : A.det = 1 := by
      rw [Matrix.det_fin_two_of]
      have h1 : E 0 0 * E 1 1 - E 0 1 * E 1 0 = 1 := by
        have := Matrix.det_fin_two (E : Matrix (Fin 2) (Fin 2) ℤ)
        rw [Matrix.SpecialLinearGroup.det_coe] at this
        linarith
      calc E 0 0 * E 1 1 - E 0 1 * ℓ * (E 1 0 / ℓ)
          = E 0 0 * E 1 1 - E 0 1 * (ℓ * (E 1 0 / ℓ)) := by ring
        _ = 1 := by rw [Int.mul_ediv_cancel' hℓc, h1]
    have hA0 : (⟨A, hdet⟩ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M := by
      refine CongruenceSubgroup.Gamma0_mem.mpr ?_
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      show (M : ℤ) ∣ E 1 0 / ℓ
      obtain ⟨t, ht⟩ := hc
      rw [ht, show (M : ℤ) * ℓ * t = ℓ * (M * t) by ring, Int.mul_ediv_cancel_left _ hℓ]
      exact Dvd.intro t rfl
    have hAH : (⟨A, hdet⟩ : SL(2, ℤ)) ∈ Γ := by
      refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩

      obtain ⟨hE0', hEu⟩ := CohCarrier.mem_GammaH_iff.mp hEH
      have : CohCarrier.gamma0Units M ⟨⟨A, hdet⟩, hA0⟩ = CohCarrier.gamma0Units M ⟨E, hE0'⟩ := by
        apply Units.ext
        rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
        rfl
      rw [this]; exact hEu
    have hAU : (⟨_, hAH⟩ : Γ) ∈ U := by
      rw [Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]
      show (ℓ : ℤ) ∣ E 0 1 * ℓ
      exact Dvd.intro_left _ rfl
    refine ⟨⟨_, hAU⟩, ?_⟩
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [coe_up]
    fin_cases i <;> fin_cases j
    · simp [CohCarrier.conjUpperMat, A]
    · simp [CohCarrier.conjUpperMat, A, Int.mul_ediv_cancel _ hℓ]
    · simp [CohCarrier.conjUpperMat, A, Int.ediv_mul_cancel hℓc]
    · simp [CohCarrier.conjUpperMat, A]

end Up

section Moebius

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} (ℓ : ℕ) [Fact ℓ.Prime]

theorem heckeDiag_smul_heckeMatrix_zero (u : ℍ) :
    ModularForm.heckeDiagMatrix ℓ • (ModularForm.heckeMatrix ℓ 0 • u) = u := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ), ModularForm.coe_heckeMatrix_smul (hℓ0 ℓ)]
  have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0 ℓ
  field_simp
  push_cast
  ring

theorem heckeMatrix_zero_smul_heckeDiag (u : ℍ) :
    ModularForm.heckeMatrix ℓ 0 • (ModularForm.heckeDiagMatrix ℓ • u) = u := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeMatrix_smul (hℓ0 ℓ), ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ)]
  have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0 ℓ
  field_simp
  push_cast
  ring

theorem heckeDiag_smul_heckeMatrix (j : ℕ) (τ : ℍ) :
    ModularForm.heckeDiagMatrix ℓ • (ModularForm.heckeMatrix ℓ j • τ) =
      (ModularGroup.T ^ (j : ℤ)) • τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ), ModularForm.coe_heckeMatrix_smul (hℓ0 ℓ),
    UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0 ℓ
  field_simp
  push_cast
  ring

omit [Fact ℓ.Prime] in

theorem coe_sl_smul (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) =
      ((g 0 0 : ℤ) * (z : ℂ) + (g 0 1 : ℤ)) / ((g 1 0 : ℤ) * (z : ℂ) + (g 1 1 : ℤ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

omit [Fact ℓ.Prime] in
theorem sl_denom_ne_zero (g : SL(2, ℤ)) (z : ℍ) :
    ((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) z
  rw [UpperHalfPlane.denom] at this
  simpa using this

theorem conjUpperMat_smul (h : SL(2, ℤ)) (hdvd : (ℓ : ℤ) ∣ h 0 1) (v : ℍ) :
    (CohCarrier.conjUpperMat ℓ h hdvd) • v =
      ModularForm.heckeMatrix ℓ 0 • (h • (ModularForm.heckeDiagMatrix ℓ • v)) := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeMatrix_smul (hℓ0 ℓ), coe_sl_smul, coe_sl_smul,
    ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ)]
  simp only [(conjUpperMat_apply ℓ h hdvd).1, (conjUpperMat_apply ℓ h hdvd).2.1, (conjUpperMat_apply ℓ h hdvd).2.2.1,
    (conjUpperMat_apply ℓ h hdvd).2.2.2]
  obtain ⟨b', hb'⟩ := hdvd
  rw [hb', Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ0 ℓ : (ℓ : ℤ) ≠ 0)]
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0 ℓ
  have hden : ((h 1 0 : ℤ) : ℂ) * ((ℓ : ℂ) * (v : ℂ)) + ((h 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (h : GL (Fin 2) ℝ) (ModularForm.heckeDiagMatrix ℓ • v)
    rw [UpperHalfPlane.denom, ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ)] at this
    simpa using this
  push_cast
  field_simp
  ring

theorem heckeDiag_smul_gPrime_smul [NeZero M] (hN : ¬ ℓ ∣ M) (τ : ℍ) :
    ModularForm.heckeDiagMatrix ℓ •
        (((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) •
          (ModularForm.heckeDiagMatrix ℓ • τ)) =
      ((gInf M H ℓ : CohCarrier.GammaH M H) : SL(2, ℤ)) • τ := by
  apply UpperHalfPlane.ext
  have hden1 := sl_denom_ne_zero ((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ))
    (ModularForm.heckeDiagMatrix ℓ • τ)
  have hden2 := sl_denom_ne_zero ((gInf M H ℓ : CohCarrier.GammaH M H) : SL(2, ℤ)) τ
  rw [ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ)] at hden1
  rw [ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ), coe_sl_smul, coe_sl_smul,
    ModularForm.coe_heckeDiagMatrix_smul (hℓ0 ℓ)]
  rw [(gPrime_apply M ℓ hN).2.2.1, (gPrime_apply M ℓ hN).2.2.2] at hden1
  rw [(gInf_apply M H ℓ hN).2.2.1, (gInf_apply M H ℓ hN).2.2.2] at hden2
  simp only [(gPrime_apply M ℓ hN).1, (gPrime_apply M ℓ hN).2.1, (gPrime_apply M ℓ hN).2.2.1,
    (gPrime_apply M ℓ hN).2.2.2, (gInf_apply M H ℓ hN).1, (gInf_apply M H ℓ hN).2.1,
    (gInf_apply M H ℓ hN).2.2.1, (gInf_apply M H ℓ hN).2.2.2] at hden1 hden2 ⊢
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0 ℓ
  push_cast at hden1 hden2 ⊢
  have hden1' : (M : ℂ) * (τ : ℂ) + 1 ≠ 0 := by
    intro h0; apply hden1; linear_combination (ℓ : ℂ) * h0
  field_simp

end Moebius

section RamCount

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Γ" => CohCarrier.GammaH M H
local notation "U" => CohCarrier.GammaHUpper M H ℓ
local notation "Γ'" => (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

omit [NeZero M] [Fact ℓ.Prime] in

theorem upper_smul (h : U) (v : ℍ) : h • v = ((h : Γ) : SL(2, ℤ)) • v := rfl

omit [NeZero M] [Fact ℓ.Prime] in
theorem top_smul (g : ↥Γ') (v : ℍ) : g • v = (g : SL(2, ℤ)) • v := rfl

omit [NeZero M] in

theorem card_stabilizer_up (w : ℍ) :
    Nat.card (MulAction.stabilizer (↥Γ') w) =
      Nat.card (MulAction.stabilizer U (ModularForm.heckeDiagMatrix ℓ • w)) := by
  haveI : NeZero ℓ := ⟨hℓ0 ℓ⟩
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective (up M H ℓ) (up_bijective M H ℓ)) ?_)
  intro h
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Equiv.ofBijective_apply,
    upper_smul, top_smul, coe_up, conjUpperMat_smul]
  conv_rhs => rw [← heckeMatrix_zero_smul_heckeDiag ℓ w]
  rw [smul_left_cancel_iff, heckeDiag_smul_heckeMatrix_zero]

end RamCount

section Fibre

open AlgebraicCurve

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem comp_aeval_toRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A]
    [Algebra ℤ B] (f : A →+* B) (y : A) :
    f.comp (Polynomial.aeval (R := ℤ) y).toRingHom =
      (Polynomial.aeval (R := ℤ) (f y)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a; simp [eq_intCast]
  · simp

theorem aeval_mem_of_mem {A : Type*} [CommRing A] [Algebra ℤ A] {S : Type*} [SetLike S A]
    [SubringClass S A] (s : S) {x : A} (hx : x ∈ s) (p : Polynomial ℤ) :
    Polynomial.aeval x p ∈ s := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, eq_intCast]
    exact mul_mem (intCast_mem s a) (pow_mem hx n)

theorem jq_mem_qExpFunctionFieldC (Δ : Subgroup SL(2, ℤ)) : jq ∈ qExpFunctionFieldC ℚ Δ := by
  have h := ModularCurve.jqModC_mem_intFormRatiosC ℚ Δ
  rw [jqModC_rat] at h
  exact intFormRatiosC_subset ℚ Δ h

theorem le_SL (Δ : Subgroup SL(2, ℤ)) : ((Δ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    {k : ℤ} (f : F) [ModularFormClass F Γ k] : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

@[scoped simp]
theorem coe_restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (hle : Γ' ≤ Γ) {k : ℤ} (f : F) [ModularFormClass F Γ k] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

def GΔ (Δ : Subgroup SL(2, ℤ)) : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Δ) (ModularForm.mcast (by decide) (ModularForm.E₄.pow 3))

def HΔ (Δ : Subgroup SL(2, ℤ)) : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Δ) CuspForm.discriminant

theorem coe_GΔ (Δ : Subgroup SL(2, ℤ)) : ((GΔ Δ : ModularForm _ 12) : ℍ → ℂ) =
    ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl

theorem coe_HΔ (Δ : Subgroup SL(2, ℤ)) : ((HΔ Δ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem HΔ_apply_ne_zero (Δ : Subgroup SL(2, ℤ)) (z : ℍ) : (HΔ Δ : ℍ → ℂ) z ≠ 0 := by
  rw [coe_HΔ]
  exact ModularForm.discriminant_ne_zero z

abbrev qL {Δ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) :
    LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods_of_T_mem {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    (1 : ℝ) ∈ ((Δ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem continuous_coe {Δ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) :
    Continuous (f : ℍ → ℂ) :=
  (ModularFormClass.holo f).continuous

theorem qL_ne_zero {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) {k : ℤ}
    (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) : qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem HΔ_ne_zero (Δ : Subgroup SL(2, ℤ)) : HΔ Δ ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 12 => (f : ℍ → ℂ) I) h
  exact HΔ_apply_ne_zero Δ I (by simpa using this)

theorem qL_GΔ (Δ : Subgroup SL(2, ℤ)) : qL (GΔ Δ) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have h : qExpansion 1 ((GΔ Δ : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [coe_GΔ, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

theorem qL_HΔ (Δ : Subgroup SL(2, ℤ)) : qL (HΔ Δ) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem coeffEmb_jq_eq : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℂ)

theorem coeffEmb_jq_mul_qL_HΔ {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    coeffEmb ℂ jq * qL (HΔ Δ) = qL (GΔ Δ) := by
  rw [coeffEmb_jq_eq, jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_GΔ, ← qL_HΔ]
  exact div_mul_cancel₀ _ (qL_ne_zero hT (HΔ Δ) (HΔ_ne_zero Δ))

theorem realizeOf_coeffEmb_jq {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) (z : ℍ) :
    realizeOf Δ (coeffEmb ℂ jq) z = (GΔ Δ : ℍ → ℂ) z / (HΔ Δ : ℍ → ℂ) z :=
  ModularCurve.realizeOf_eq_div Δ hT (GΔ Δ) (HΔ Δ) (coeffEmb ℂ jq) (coeffEmb_jq_mul_qL_HΔ hT) z
    (HΔ_apply_ne_zero Δ z)

theorem isBoundedUnder_realizeOf_coeffEmb_jq {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realizeOf Δ (coeffEmb ℂ jq) z‖) := by
  have hcont : Continuous (fun z : ℍ => (GΔ Δ : ℍ → ℂ) z / (HΔ Δ : ℍ → ℂ) z) :=
    (continuous_coe (GΔ Δ)).div (continuous_coe (HΔ Δ)) (HΔ_apply_ne_zero Δ)
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(GΔ Δ : ℍ → ℂ) z / (HΔ Δ : ℍ → ℂ) z‖) :=
    (hcont.continuousAt.norm.tendsto).isBoundedUnder_le
  have hfun : (fun z : ℍ => ‖realizeOf Δ (coeffEmb ℂ jq) z‖) =
      fun z : ℍ => ‖(GΔ Δ : ℍ → ℂ) z / (HΔ Δ : ℍ → ℂ) z‖ :=
    funext fun z => by rw [realizeOf_coeffEmb_jq hT]
  rw [hfun]
  exact hbd.mono nhdsWithin_le_nhds

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

local notation "ΓH" => CohCarrier.GammaH M H
local notation "ΓT" => (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

abbrev CF : Type := ↥(laurentBaseChange ℂ (xHFunctionField M H))

abbrev CF' : Type := ↥(laurentBaseChange ℂ (xHTopFunctionFieldC ℚ M H (M * ℓ)))

def jX : CF M H :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_qExpFunctionFieldC (ΓH))⟩

def jX' : CF' M H ℓ :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_qExpFunctionFieldC (ΓT))⟩

@[scoped simp] theorem coe_jX : ((jX M H : CF M H) : LaurentSeries ℂ) = coeffEmb ℂ jq := rfl
@[scoped simp] theorem coe_jX' : ((jX' M H ℓ : CF' M H ℓ) : LaurentSeries ℂ) = coeffEmb ℂ jq := rfl

theorem jX_mem_pt (D : ComplexPlaceDictionaryOf (ΓH) (xHFunctionField M H)) (τ : ℍ) :
    jX M H ∈ (D.pt τ).toValuationSubring :=
  (D.mem_pt_iff τ (jX M H)).mpr (isBoundedUnder_realizeOf_coeffEmb_jq (translation_mem_GammaH M H) τ)

theorem T_mem_top : ModularGroup.T ∈ (ΓT) := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [ModularGroup.T]

theorem jX'_mem_pt (D' : ComplexPlaceDictionaryOf (ΓT) (xHTopFunctionFieldC ℚ M H (M * ℓ))) (τ : ℍ) :
    jX' M H ℓ ∈ (D'.pt τ).toValuationSubring :=
  (D'.mem_pt_iff τ (jX' M H ℓ)).mpr (isBoundedUnder_realizeOf_coeffEmb_jq (T_mem_top M H ℓ) τ)

theorem coeffEmb_qExpand_eq (d : ℕ) [NeZero d] (x : LaurentSeries ℚ) :
    coeffEmb ℂ (qExpand ℚ d x) = qExpand ℂ d (coeffEmb ℂ x) := by
  ext k
  by_cases hk : (d : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd (hk := hk), qExpand_coeff_of_not_dvd (hk := hk),
      map_zero]

variable [NeZero ℓ]

theorem coe_heckeBetaHBar_jX (h0 : HeckeBetaHDefined M H ℓ) :
    ((heckeBetaHBar ℂ M H ℓ (jX M H) : CF' M H ℓ) : LaurentSeries ℂ) = coeffEmb ℂ (qExpand ℚ ℓ jq) := by
  rw [coe_heckeBetaHBar M H ℓ h0, coe_jX, coeffEmb_qExpand_eq]

theorem eval_map_Phi_jX [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) (data : ModularPolynomialData ℓ)
    (hsymm : EvalSymm data.Φ) :
    (data.Φ.map (Polynomial.aeval (R := ℤ) (heckeBetaHBar ℂ M H ℓ (jX M H))).toRingHom).eval
        (jX' M H ℓ) = 0 := by
  rw [Polynomial.eval_map]
  have hℚ : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (qExpand ℚ ℓ jq)).toRingHom jq = 0 := by
    rw [← hsymm]; exact data.eval_eq_zero
  have hℂ : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (coeffEmb ℂ (qExpand ℚ ℓ jq))).toRingHom
      (coeffEmb ℂ jq) = 0 := by
    have := congrArg (coeffEmb ℂ) hℚ
    rwa [Polynomial.hom_eval₂, comp_aeval_toRingHom, map_zero] at this
  set v : CF' M H ℓ →+* LaurentSeries ℂ :=
    (IntermediateField.val (laurentBaseChange ℂ (xHTopFunctionFieldC ℚ M H (M * ℓ)))).toRingHom
  have hv : Function.Injective v := Subtype.val_injective
  rw [← map_eq_zero_iff v hv, Polynomial.hom_eval₂, comp_aeval_toRingHom]
  have h1 : v (heckeBetaHBar ℂ M H ℓ (jX M H)) = coeffEmb ℂ (qExpand ℚ ℓ jq) :=
    coe_heckeBetaHBar_jX M H ℓ h0
  have h2 : v (jX' M H ℓ) = coeffEmb ℂ jq := rfl
  rw [h1, h2]
  convert hℂ

theorem exists_pt_eq_of_restrictAlong_beta [Fact ℓ.Prime]
    (D : ComplexPlaceDictionaryOf (ΓH) (xHFunctionField M H))
    (D' : ComplexPlaceDictionaryOf (ΓT) (xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (h0 : HeckeBetaHDefined M H ℓ) (hβ : HeckeBetaHBarIntegral ℂ M H ℓ)
    (W : Place ℂ (CF' M H ℓ)) (τ : ℍ)
    (hW : W.restrictAlong (heckeBetaHBar ℂ M H ℓ) hβ = D.pt τ) :
    ∃ w : ℍ, D'.pt w = W := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
  have hβj : heckeBetaHBar ℂ M H ℓ (jX M H) ∈ W.toValuationSubring := by
    rw [← mem_restrictAlong_iff (heckeBetaHBar ℂ M H ℓ) hβ, hW]
    exact jX_mem_pt M H D τ
  haveI : Subgroup.FiniteIndex (ΓT) := by
    haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
    haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
    infer_instance
  refine ComplexPlaceDictionaryOf.exists_pt_eq_of_mem (ΓT) (T_mem_top M H ℓ)
    (xHTopFunctionFieldC ℚ M H (M * ℓ)) rfl D' W (jX' M H ℓ) (by rw [coe_jX', coeffEmb_jq_eq]) ?_
  refine W.mem_of_eval_monic_eq_zero
    (P := data.Φ.map (Polynomial.aeval (R := ℤ) (heckeBetaHBar ℂ M H ℓ (jX M H))).toRingHom)
    (data.monic.map _) (fun i => ?_) (eval_map_Phi_jX M H ℓ h0 data hsymm)
  rw [Polynomial.coeff_map]
  exact aeval_mem_of_mem W.toValuationSubring hβj (data.Φ.coeff i)

end Fibre

section Levels

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ℓ : ℕ) [NeZero ℓ]

local notation "Γ" => CohCarrier.GammaH M H
local notation "Γ'" => (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

omit [NeZero M] in
theorem T_mem : ModularGroup.T ∈ Γ := translation_mem_GammaH M H

scoped instance top_finiteIndex : (Γ').FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  haveI : (CohCarrier.GammaH M H).FiniteIndex := inferInstance
  infer_instance

omit [NeZero M] [NeZero ℓ] in

theorem neg_one_mem_top_iff : (-1 : SL(2, ℤ)) ∈ Γ' ↔ (-1 : SL(2, ℤ)) ∈ Γ := by
  rw [Subgroup.mem_inf]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [CongruenceSubgroup.Gamma0_mem]; simp

theorem pt_eq_pt_iff_of_eq_gammaH {Δ : Subgroup SL(2, ℤ)} {F : IntermediateField ℚ (LaurentSeries ℚ)}
    (N : ℕ) [NeZero N] (K : Subgroup (ZMod N)ˣ) (hΔ : Δ = CohCarrier.GammaH N K)
    (hF : F = xHFunctionField N K) (E : ComplexPlaceDictionaryOf Δ F) (τ τ' : ℍ) :
    E.pt τ = E.pt τ' ↔ ∃ γ ∈ Δ, γ • τ = τ' := by
  subst hΔ hF
  exact ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH N K E τ τ'

theorem sep_bot (D : ComplexPlaceDictionaryOf Γ (xHFunctionField M H)) (τ τ' : ℍ) :
    D.pt τ = D.pt τ' → ∃ γ ∈ Γ, γ • τ = τ' :=
  (ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH M H D τ τ').mp

theorem pt_eq_pt_iff_top (D' : ComplexPlaceDictionaryOf Γ' (xHTopFunctionFieldC ℚ M H (M * ℓ))) (τ τ' : ℍ) :
    D'.pt τ = D'.pt τ' ↔ ∃ γ ∈ Γ', γ • τ = τ' := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  exact pt_eq_pt_iff_of_eq_gammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ)))
    (CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap M ℓ H)
    (ModularCurve.xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap M ℓ H) D' τ τ'

theorem sep_top (D' : ComplexPlaceDictionaryOf Γ' (xHTopFunctionFieldC ℚ M H (M * ℓ))) (τ τ' : ℍ) :
    D'.pt τ = D'.pt τ' → ∃ γ ∈ Γ', γ • τ = τ' :=
  (pt_eq_pt_iff_top ℓ D' τ τ').mp

omit [NeZero M] [NeZero ℓ] in

theorem card_inf_zpowers_mul_ramification (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex]
    (hT : ModularGroup.T ∈ Δ) (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = qExpFunctionFieldC ℚ Δ) (E : ComplexPlaceDictionaryOf Δ F₀)
    (hsep : ∀ τ τ' : ℍ, E.pt τ = E.pt τ' → ∃ γ ∈ Δ, γ • τ = τ') (τ : ℍ) :
    Nat.card (Δ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) * E.ramification τ =
      Nat.card (MulAction.stabilizer Δ τ) := by
  have h1 := ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer Δ hT F₀ hF E hsep τ
  have h2 := ModularCurve.card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer Δ τ
  have h3 : 2 * (Nat.card (Δ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) * E.ramification τ) =
      2 * Nat.card (MulAction.stabilizer Δ τ) := by
    rw [mul_left_comm, h1, mul_comm, h2]
  omega

omit [NeZero M] [NeZero ℓ] in
theorem card_inf_zpowers_pos (Δ : Subgroup SL(2, ℤ)) :
    0 < Nat.card (Δ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) := by
  have hfin : ((Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)).Finite :=
    IsOfFinOrder.finite_zpowers (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by simp⟩)
  haveI : Finite (Δ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) :=
    (hfin.subset (fun x hx => (Subgroup.mem_inf.mp hx).2)).to_subtype
  exact Nat.card_pos

omit [NeZero M] [NeZero ℓ] in

theorem top_inf_zpowers_eq :
    Γ' ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) = Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
  rw [inf_assoc]
  congr 1
  refine inf_eq_right.mpr (Subgroup.zpowers_le.mpr ?_)
  rw [CongruenceSubgroup.Gamma0_mem]; simp

theorem restrictAlong_pt_heckeBetaHBar (h0 : HeckeBetaHDefined M H ℓ)
    (D : ComplexPlaceDictionaryOf Γ (xHFunctionField M H))
    (D' : ComplexPlaceDictionaryOf Γ' (xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (hβ : HeckeBetaHBarIntegral ℂ M H ℓ) (w : ℍ) :
    (D'.pt w).restrictAlong (heckeBetaHBar ℂ M H ℓ) hβ = D.pt (ModularForm.heckeDiagMatrix ℓ • w) ∧
      D'.ramification w * (D'.pt w).ramificationIndexAlong (heckeBetaHBar ℂ M H ℓ) =
        D.ramification (ModularForm.heckeDiagMatrix ℓ • w) :=
  ComplexPlaceDictionaryOf.restrictAlong_pt_qExpand Γ Γ' (T_mem (M := M) (H := H))
    (T_mem_top M H ℓ) ℓ (CohCarrier.GammaH_inf_Gamma0_le_conjGL M H ℓ)
    (xHFunctionField M H) (xHTopFunctionFieldC ℚ M H (M * ℓ)) D D'
    (heckeBetaHBar ℂ M H ℓ) (coe_heckeBetaHBar M H ℓ h0) hβ w

theorem restrictAlong_pt_heckeAlphaHBar
    (D : ComplexPlaceDictionaryOf Γ (xHFunctionField M H))
    (D' : ComplexPlaceDictionaryOf Γ' (xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (hα : HeckeAlphaHBarIntegral ℂ M H ℓ) (w : ℍ) :
    (D'.pt w).restrictAlong (heckeAlphaHBar ℂ M H ℓ) hα = D.pt w :=
  ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le (inf_le_left : Γ' ≤ Γ)
    (T_mem_top M H ℓ) rfl D D' (heckeAlphaHBar ℂ M H ℓ) (coe_heckeAlphaHBar M H ℓ) hα w

theorem inertiaDegAlong_heckeAlphaHBar_eq_one (hα : HeckeAlphaHBarIntegral ℂ M H ℓ)
    (W : Place ℂ (laurentBaseChange ℂ (xHTopFunctionFieldC ℚ M H (M * ℓ)))) :
    W.inertiaDegAlong (heckeAlphaHBar ℂ M H ℓ) hα = 1 :=
  ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (Γ') (T_mem_top M H ℓ)
    (xHTopFunctionFieldC ℚ M H (M * ℓ)) rfl (heckeAlphaHBar ℂ M H ℓ) hα W

end Levels

section RamCount2

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Γ" => CohCarrier.GammaH M H
local notation "U" => CohCarrier.GammaHUpper M H ℓ
local notation "Γ'" => (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

theorem pt_eq_pt_iff_mem_orbit
    (D' : ComplexPlaceDictionaryOf Γ' (xHTopFunctionFieldC ℚ M H (M * ℓ))) (w w₀ : ℍ) :
    D'.pt w = D'.pt w₀ ↔
      ModularForm.heckeDiagMatrix ℓ • w ∈
        MulAction.orbit U (ModularForm.heckeDiagMatrix ℓ • w₀) := by
  haveI : NeZero ℓ := ⟨hℓ0 ℓ⟩
  have key := pt_eq_pt_iff_top ℓ D' w w₀
  rw [key, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨ε, hε, hεw⟩
    obtain ⟨h, hh⟩ := (up_bijective M H ℓ).2 ⟨ε, hε⟩
    refine ⟨h⁻¹, ?_⟩
    have hε' : (CohCarrier.conjUpperMat ℓ (h : SL(2, ℤ)) (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h)) • w = w₀ := by
      have := congrArg (fun g : ↥Γ' => (g : SL(2, ℤ))) hh
      simp only [coe_up] at this
      rw [this]; exact hεw
    rw [inv_smul_eq_iff, upper_smul, ← heckeDiag_smul_heckeMatrix_zero ℓ
      (((h : Γ) : SL(2, ℤ)) • (ModularForm.heckeDiagMatrix ℓ • w)),
      ← conjUpperMat_smul ℓ _ (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ h), hε']
  · rintro ⟨h, hh⟩
    refine ⟨(up M H ℓ h⁻¹ : ↥Γ'), (up M H ℓ h⁻¹).2, ?_⟩
    rw [coe_up, conjUpperMat_smul]
    show ModularForm.heckeMatrix ℓ 0 • ((((h⁻¹ : U) : Γ) : SL(2, ℤ)) • (ModularForm.heckeDiagMatrix ℓ • w)) = w₀
    rw [← upper_smul, ← hh, inv_smul_smul, heckeMatrix_zero_smul_heckeDiag]

theorem ramificationIndexAlong_eq_card
    (D : ComplexPlaceDictionaryOf Γ (xHFunctionField M H))
    (D' : ComplexPlaceDictionaryOf Γ' (xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (h0 : HeckeBetaHDefined M H ℓ) (hβ : HeckeBetaHBarIntegral ℂ M H ℓ)
    (w₀ τ : ℍ) (g₀ : Γ)
    (hg₀ : g₀ • τ = ModularForm.heckeDiagMatrix ℓ • w₀)
    [DecidablePred fun i => rep M H ℓ i • τ ∈
      MulAction.orbit U (ModularForm.heckeDiagMatrix ℓ • w₀)] :
    haveI : NeZero ℓ := ⟨hℓ0 ℓ⟩
    (D'.pt w₀).ramificationIndexAlong (heckeBetaHBar ℂ M H ℓ) =
      ((idxSet M ℓ).filter fun i => rep M H ℓ i • τ ∈
        MulAction.orbit U (ModularForm.heckeDiagMatrix ℓ • w₀)).card := by
  haveI : NeZero ℓ := ⟨hℓ0 ℓ⟩
  have hcount := card_stabilizer_eq_card_filter_mul U (rep M H ℓ)
    (idxSet M ℓ) (cover M H ℓ) (disjoint M H ℓ) τ (ModularForm.heckeDiagMatrix ℓ • w₀) g₀ hg₀

  set c : ℕ := Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) with hc_def
  have hc : 0 < c := card_inf_zpowers_pos Γ
  have hC3x : c * D.ramification (ModularForm.heckeDiagMatrix ℓ • w₀) =
      Nat.card (MulAction.stabilizer Γ (ModularForm.heckeDiagMatrix ℓ • w₀)) :=
    card_inf_zpowers_mul_ramification Γ (T_mem (M := M) (H := H)) _ rfl D (sep_bot D) _
  have hC3w : c * D'.ramification w₀ = Nat.card (MulAction.stabilizer (↥Γ') w₀) := by
    rw [hc_def, ← top_inf_zpowers_eq ℓ]
    exact card_inf_zpowers_mul_ramification Γ' (T_mem_top M H ℓ) _ rfl D' (sep_top ℓ D') w₀
  have htrans := card_stabilizer_up (M := M) (H := H) ℓ w₀
  have hC2 := (restrictAlong_pt_heckeBetaHBar ℓ h0 D D' hβ w₀).2
  have hpos : 0 < c * D'.ramification w₀ := Nat.mul_pos hc (D'.ramification_pos w₀)
  refine (Nat.eq_of_mul_eq_mul_right hpos ?_).symm
  calc ((idxSet M ℓ).filter fun i => rep M H ℓ i • τ ∈
          MulAction.orbit U (ModularForm.heckeDiagMatrix ℓ • w₀)).card * (c * D'.ramification w₀)
      = ((idxSet M ℓ).filter fun i => rep M H ℓ i • τ ∈
          MulAction.orbit U (ModularForm.heckeDiagMatrix ℓ • w₀)).card *
          Nat.card (MulAction.stabilizer U (ModularForm.heckeDiagMatrix ℓ • w₀)) := by rw [hC3w, htrans]
    _ = Nat.card (MulAction.stabilizer Γ (ModularForm.heckeDiagMatrix ℓ • w₀)) := hcount.symm
    _ = c * D.ramification (ModularForm.heckeDiagMatrix ℓ • w₀) := hC3x.symm
    _ = c * (D'.ramification w₀ * (D'.pt w₀).ramificationIndexAlong (heckeBetaHBar ℂ M H ℓ)) := by
          rw [hC2]
    _ = (D'.pt w₀).ramificationIndexAlong (heckeBetaHBar ℂ M H ℓ) * (c * D'.ramification w₀) := by
          ring

end RamCount2

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

omit [NeZero M] in

theorem mul_inv_mem_GammaH (ρ σ : CongruenceSubgroup.Gamma0 M)
    (h : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(ρ * σ⁻¹).2, ?_⟩
  have hu : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ :=
    Units.ext (by rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]; exact h)
  have : CohCarrier.gamma0Units M ⟨(ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹, (ρ * σ⁻¹).2⟩ =
      CohCarrier.gamma0Units M (ρ * σ⁻¹) := rfl
  rw [this, map_mul, map_inv, hu, mul_inv_cancel]
  exact one_mem H

theorem main
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : ModularCurve.HeckeBetaHDefined M H ℓ)
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (τ : UpperHalfPlane) :
    (∀ (hℓM : ¬ ℓ ∣ M) (ρ : CongruenceSubgroup.Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1 +
          Finsupp.single (D.pt (((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) • τ)) 1) ∧
    (ℓ ∣ M →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  obtain ⟨D'⟩ := ModularCurve.exists_complexPlaceDictionaryOf
    (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (T_mem_top M H ℓ)
    (xHTopFunctionFieldC ℚ M H (M * ℓ)) rfl
  set β := heckeBetaHBar ℂ M H ℓ with hβdef
  set α := heckeAlphaHBar ℂ M H ℓ with hαdef
  set dg := ModularForm.heckeDiagMatrix ℓ with hdg
  set F := Place.fiberAlong β hβ (D.pt τ) with hF

  have hLHS : heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
      ∑ W ∈ F, Finsupp.single (W.restrictAlong α hα) ((W.ramificationIndexAlong β : ℕ) : ℤ) := by
    show Divisor.correspondence β α hβ hα (Finsupp.single (D.pt τ) 1) = _
    rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [Divisor.pushforwardAlong_single, inertiaDegAlong_heckeAlphaHBar_eq_one ℓ hα W]
    simp

  let w' : Option (Fin ℓ) → ℍ := fun i =>
    match i with
    | some j => ModularForm.heckeMatrix ℓ j • τ
    | none => ((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) • (dg • τ)
  have hkey : ∀ i ∈ idxSet M ℓ,
      dg • w' i = ((rep M H ℓ i : CohCarrier.GammaH M H) : SL(2, ℤ)) • τ := by
    intro i hi
    cases i with
    | some j => exact heckeDiag_smul_heckeMatrix ℓ j τ
    | none => exact heckeDiag_smul_gPrime_smul (H := H) ℓ ((none_mem_idxSet M ℓ).mp hi) τ

  have hmain : heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
      ∑ i ∈ idxSet M ℓ, Finsupp.single (D.pt (w' i)) 1 := by
    rw [hLHS]

    have hmaps : ∀ i ∈ idxSet M ℓ, D'.pt (w' i) ∈ F := by
      intro i hi
      rw [hF, Place.mem_fiberAlong, (restrictAlong_pt_heckeBetaHBar ℓ h0 D D' hβ
        (w' i)).1, ← hdg, hkey i hi, D.pt_smul]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun W hW => ?_

    rw [hF, Place.mem_fiberAlong] at hW
    obtain ⟨w₀, rfl⟩ := exists_pt_eq_of_restrictAlong_beta M H ℓ D D' h0 hβ W τ hW
    have hx : D.pt (dg • w₀) = D.pt τ := by
      rw [← hW]; exact ((restrictAlong_pt_heckeBetaHBar ℓ h0 D D' hβ w₀).1).symm
    obtain ⟨g₀, hg₀mem, hg₀⟩ := sep_bot D τ (dg • w₀) hx.symm

    have hinner : ∀ i ∈ (idxSet M ℓ).filter (fun i => D'.pt (w' i) = D'.pt w₀),
        (Finsupp.single (D.pt (w' i)) 1 : Divisor ℂ (laurentBaseChange ℂ (xHFunctionField M H)))
          = Finsupp.single ((D'.pt w₀).restrictAlong α hα) 1 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [← hi.2, restrictAlong_pt_heckeAlphaHBar ℓ D D' hα (w' i)]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finsupp.smul_single, nsmul_eq_mul, mul_one]
    congr 1

    rw [ramificationIndexAlong_eq_card ℓ D D' h0 hβ w₀ τ ⟨g₀, hg₀mem⟩ hg₀]
    congr 1
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    rw [pt_eq_pt_iff_mem_orbit ℓ D' (w' i) w₀, ← hdg, hkey i hi]
    rfl

  refine ⟨fun hℓM ρ hρ => ?_, fun hℓM => ?_⟩
  · rw [hmain, idxSet, Finset.sum_filter, Fintype.sum_option, Finset.sum_range]
    have hρpt : D.pt (((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * dg) • τ) = D.pt (w' none) := by
      show D.pt (((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * dg) • τ) =
        D.pt (((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) • (dg • τ))
      have hmem := mul_inv_mem_GammaH M H ρ (gPrime M ℓ) (by rw [hρ, gPrime_apply_11_mod M ℓ hℓM])
      have := D.pt_smul_of_mem hmem (((gPrime M ℓ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) • (dg • τ))
      rw [← this, ← mul_smul, inv_mul_cancel_right, mul_smul]
      rfl
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, false_or, true_or, if_true,
      if_pos hℓM, hρpt]
    rw [add_comm]
  · rw [hmain, idxSet, Finset.sum_filter, Fintype.sum_option, Finset.sum_range]
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, false_or, true_or, if_true,
      if_neg (not_not.mpr hℓM), zero_add]
    rfl

end Main

end ModularCurve.HeckeDivHBarSinglePt
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.ModularCurve.HeckeDivHBarSinglePt"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.ModularCurve.HeckeDivHBarSinglePt"

open UpperHalfPlane in
open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : ModularCurve.HeckeBetaHDefined M H ℓ)
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (τ : UpperHalfPlane) :
    (∀ (hℓM : ¬ ℓ ∣ M) (ρ : CongruenceSubgroup.Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1 +
          Finsupp.single (D.pt (((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) • τ)) 1) ∧
    (ℓ ∣ M →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1) :=
  ModularCurve.HeckeDivHBarSinglePt.main M H D ℓ hℓ h0 hα hβ τ

end S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt (solution)
