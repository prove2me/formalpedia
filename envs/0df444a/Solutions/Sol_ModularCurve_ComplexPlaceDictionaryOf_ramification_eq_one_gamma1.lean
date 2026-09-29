-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.ramification_eq_one_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/457b690c-f9e1-5d18-b6c5-68ece28bea13

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
import Theorems.Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.LevelN.coe_jGen AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm Complex SlashInvariantForm Filter ModularGroup
open scoped MatrixGroups Real Topology ModularForm Manifold Modular

namespace ModularCurve
p2m_export "ModularCurve" "mem_intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset jNum constantCoeff_jNum ofPowerSeries_coeff_of_neg algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC realizeOf ComplexPlaceDictionaryOf realizeOf_eq_div jqModC_eq_qExpansion_E4_cube_div_discriminant meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1 jqModC_mem_intFormRatiosC"
namespace RamOne
p2m_open "ModularCurve"

section JM

def jf : ℍ → ℂ := fun τ => (E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ

lemma E₄_smul (γ : SL(2, ℤ)) (τ : ℍ) : E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * E₄ τ := by
  have h := slash_action_eqn'' (Γ := 𝒮ℒ) (k := (4 : ℤ)) E₄ (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ τ
  simpa [ModularGroup.sl_moeb] using h

lemma Δ_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := slash_action_eqn'' (Γ := 𝒮ℒ) (k := (12 : ℤ)) CuspForm.discriminant
    (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ τ
  simpa [ModularGroup.sl_moeb, CuspForm.coe_discriminant] using h

lemma jf_smul (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ := by
  simp only [jf]
  rw [E₄_smul, Δ_smul]
  have hd : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hΔ := discriminant_ne_zero τ
  field_simp

lemma mdifferentiable_jf : MDiff jf :=
  (E₄.holo'.pow 3).div CuspForm.discriminant.holo' discriminant_ne_zero

lemma mdiff_E₄ : MDiff (E₄ : ℍ → ℂ) := E₄.holo'
lemma mdiff_E₆ : MDiff (E₆ : ℍ → ℂ) := E₆.holo'
lemma mdiff_Δ : MDiff (ModularForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'

lemma E₆_smul (γ : SL(2, ℤ)) (τ : ℍ) : E₆ (γ • τ) = denom γ τ ^ (6 : ℤ) * E₆ τ := by
  have h := slash_action_eqn'' (Γ := 𝒮ℒ) (k := (6 : ℤ)) E₆ (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ τ
  simpa [ModularGroup.sl_moeb] using h

lemma S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I :=
  ModularGroup.stabilizer_I.mpr (by simp)

lemma TinvS_smul_ρ : (ModularGroup.T⁻¹ * ModularGroup.S) • ρ = ρ :=
  ModularGroup.stabilizer_ρ.mpr (by simp)

lemma E₆_I : E₆ UpperHalfPlane.I = 0 := by
  have h := E₆_smul ModularGroup.S UpperHalfPlane.I
  rw [S_smul_I, ModularGroup.denom_S, UpperHalfPlane.coe_I] at h
  have hI6 : Complex.I ^ (6 : ℤ) = -1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast]
    calc Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [hI6] at h
  linear_combination h / 2

lemma denom_TinvS_ρ : denom (↑(ModularGroup.T⁻¹ * ModularGroup.S) : GL (Fin 2) ℝ) ρ = (ρ : ℂ) := by
  rw [ModularGroup.denom_apply]
  have h10 : (ModularGroup.T⁻¹ * ModularGroup.S) 1 0 = 1 := by
    change ((ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_inv, ModularGroup.coe_S]
    simp
  have h11 : (ModularGroup.T⁻¹ * ModularGroup.S) 1 1 = 0 := by
    change ((ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_inv, ModularGroup.coe_S]
    simp
  rw [h10, h11]
  simp

lemma ρ_ne_one : (ρ : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [UpperHalfPlane.coe_im] at this
  simp at this
  exact ρ.im_pos.ne' this

lemma E₄_ρ : E₄ ρ = 0 := by
  have h := E₄_smul (ModularGroup.T⁻¹ * ModularGroup.S) ρ
  rw [TinvS_smul_ρ, denom_TinvS_ρ] at h
  have hρ4 : (ρ : ℂ) ^ (4 : ℤ) = (ρ : ℂ) := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    linear_combination ((ρ : ℂ) ^ 2 - ρ) * ρ_sq
  rw [hρ4] at h
  have : ((ρ : ℂ) - 1) * E₄ ρ = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) ρ_ne_one
  · exact h1

lemma E₄_I_ne_zero : E₄ UpperHalfPlane.I ≠ 0 := by
  intro h
  have hΔ := discriminant_ne_zero UpperHalfPlane.I
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, E₆_I] at hΔ
  norm_num at hΔ

lemma E₆_ρ_ne_zero : E₆ ρ ≠ 0 := by
  intro h
  have hΔ := discriminant_ne_zero ρ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, E₄_ρ] at hΔ
  norm_num at hΔ

lemma jf_ρ : jf ρ = 0 := by simp [jf, E₄_ρ]

lemma jf_I_ne_zero : jf UpperHalfPlane.I ≠ 0 :=
  div_ne_zero (pow_ne_zero _ E₄_I_ne_zero) (discriminant_ne_zero _)

lemma E₄_smul_eq_zero_iff (γ : SL(2, ℤ)) (τ : ℍ) : E₄ (γ • τ) = 0 ↔ E₄ τ = 0 := by
  rw [E₄_smul, mul_eq_zero, or_iff_right]
  exact zpow_ne_zero _ (denom_ne_zero _ _)

lemma E₆_smul_eq_zero_iff (γ : SL(2, ℤ)) (τ : ℍ) : E₆ (γ • τ) = 0 ↔ E₆ τ = 0 := by
  rw [E₆_smul, mul_eq_zero, or_iff_right]
  exact zpow_ne_zero _ (denom_ne_zero _ _)

lemma natCard_stabilizer_I : Nat.card (MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1, ModularGroup.S, -ModularGroup.S} : Finset SL(2, ℤ)))
    (fun g => (MulAction.mem_stabilizer_iff).trans ModularGroup.stabilizer_I)),
    Nat.card_eq_finsetCard]
  decide

lemma natCard_stabilizer_ρ : Nat.card (MulAction.stabilizer SL(2, ℤ) ρ) = 6 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1, ModularGroup.S * ModularGroup.T, -(ModularGroup.S * ModularGroup.T),
      ModularGroup.T⁻¹ * ModularGroup.S, -(ModularGroup.T⁻¹ * ModularGroup.S)} : Finset SL(2, ℤ)))
    (fun g => (MulAction.mem_stabilizer_iff).trans ModularGroup.stabilizer_ρ)),
    Nat.card_eq_finsetCard]
  decide

lemma natCard_stabilizer_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) (γ • τ)) =
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : γ • τ = γ • τ)).toEquiv).symm

lemma orbit_trichotomy (τ : ℍ) :
    (∃ γ : SL(2, ℤ), τ = γ • UpperHalfPlane.I) ∨ (∃ γ : SL(2, ℤ), τ = γ • ρ) ∨
      (∀ g : SL(2, ℤ), g • τ = τ → g = 1 ∨ g = -1) := by
  obtain ⟨g₀, hg₀⟩ := ModularGroup.exists_smul_mem_fd τ
  by_cases hI : g₀ • τ = UpperHalfPlane.I
  · exact Or.inl ⟨g₀⁻¹, by rw [← hI, inv_smul_smul]⟩
  by_cases hρ : g₀ • τ = ρ
  · exact Or.inr (Or.inl ⟨g₀⁻¹, by rw [← hρ, inv_smul_smul]⟩)
  by_cases hρ' : g₀ • τ = (1 : ℝ) +ᵥ ρ
  · refine Or.inr (Or.inl ⟨g₀⁻¹ * ModularGroup.T, ?_⟩)
    rw [mul_smul, UpperHalfPlane.modular_T_smul, ← hρ', inv_smul_smul]
  refine Or.inr (Or.inr fun g hg => ?_)
  have h : (g₀ * g * g₀⁻¹) • (g₀ • τ) = g₀ • τ := by
    rw [mul_smul, mul_smul, inv_smul_smul, hg]
  rcases ModularGroup.stabilizer_of_ne hg₀ h hI hρ hρ' with h1 | h1
  · left
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h1
    simpa [mul_assoc] using this
  · right
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h1
    simpa [mul_assoc] using this

lemma natCard_stabilizer_eq_two {τ : ℍ} (h : ∀ g : SL(2, ℤ), g • τ = τ → g = 1 ∨ g = -1) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2 := by
  have hiff : ∀ g : SL(2, ℤ), g ∈ MulAction.stabilizer SL(2, ℤ) τ ↔
      g ∈ ({1, -1} : Finset SL(2, ℤ)) := by
    intro g
    rw [MulAction.mem_stabilizer_iff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h g, ?_⟩
    rintro (rfl | rfl)
    · exact one_smul _ _
    · rw [ModularGroup.SL_neg_smul, one_smul]
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1} : Finset SL(2, ℤ))) hiff), Nat.card_eq_finsetCard]
  decide

lemma E₆_ne_zero_of_E₄_eq_zero {τ : ℍ} (h4 : E₄ τ = 0) : E₆ τ ≠ 0 := by
  intro h6
  have hΔ := discriminant_ne_zero τ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h4, h6] at hΔ
  norm_num at hΔ

lemma jf_eq_of_E₆_eq_zero {τ : ℍ} (h6 : E₆ τ = 0) : jf τ = 1728 := by
  have hΔ := discriminant_ne_zero τ
  have hΔ' := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [h6] at hΔ'
  have h4 : E₄ τ ^ 3 ≠ 0 := by
    intro h
    rw [h] at hΔ'
    norm_num at hΔ'
    exact hΔ hΔ'
  simp only [jf]
  rw [div_eq_iff hΔ, hΔ']
  ring

end JM

section JREG

variable (Γ : Subgroup SL(2, ℤ))

theorem le_SL : ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
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

def G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Γ) (ModularForm.mcast (by decide) (ModularForm.E₄.pow 3))

def H : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrict (le_SL Γ) CuspForm.discriminant

theorem coe_G : ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
    ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl

theorem G_apply (z : ℍ) : (G Γ : ℍ → ℂ) z = (E₄ : ℍ → ℂ) z ^ 3 := by
  rw [coe_G, ModularForm.coe_pow, Pi.pow_apply]

theorem coe_H : ((H Γ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem H_apply_ne_zero (z : ℍ) : (H Γ : ℍ → ℂ) z ≠ 0 := by
  rw [coe_H]
  exact ModularForm.discriminant_ne_zero z

abbrev qL {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods [hT : Fact (ModularGroup.T ∈ Γ)] :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT.out, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qL_ne_zero [hT : Fact (ModularGroup.T ∈ Γ)] {k : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hf : f ≠ 0) : qL Γ f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods Γ)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem H_ne_zero : H Γ ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 => (f : ℍ → ℂ) I) h
  exact H_apply_ne_zero Γ I (by simpa using this)

theorem qL_G : qL Γ (G Γ) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have h : qExpansion 1 ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [coe_G, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

theorem qL_H : qL Γ (H Γ) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem jqModC_mul_qL_H [hT : Fact (ModularGroup.T ∈ Γ)] :
    jqModC ℂ * qL Γ (H Γ) = qL Γ (G Γ) := by
  rw [jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G, ← qL_H Γ]
  exact div_mul_cancel₀ _ (qL_ne_zero Γ (H Γ) (H_ne_zero Γ))

theorem qL_G_sub_smul_H [hT : Fact (ModularGroup.T ∈ Γ)] (c : ℂ) :
    qL Γ (G Γ - c • H Γ) = qL Γ (G Γ) - HahnSeries.C c * qL Γ (H Γ) := by
  simp only [qL]
  rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods Γ) (G Γ) (c • H Γ),
    PowerSeries.coe_sub, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods Γ) c (H Γ), PowerSeries.coe_smul,
    HahnSeries.C_mul_eq_smul]

theorem jqModC_sub_mul_qL_H [hT : Fact (ModularGroup.T ∈ Γ)] (c : ℂ) :
    (jqModC ℂ - HahnSeries.C c) * qL Γ (H Γ) = qL Γ (G Γ - c • H Γ) := by
  rw [sub_mul, jqModC_mul_qL_H, qL_G_sub_smul_H]

theorem realizeOf_jqModC_sub [hT : Fact (ModularGroup.T ∈ Γ)] (c : ℂ) (z : ℍ) :
    realizeOf Γ (jqModC ℂ - HahnSeries.C c) z = (E₄ : ℍ → ℂ) z ^ 3 / ModularForm.discriminant z - c := by
  rw [ModularCurve.realizeOf_eq_div Γ hT.out (G Γ - c • H Γ) (H Γ) _ (jqModC_sub_mul_qL_H Γ c) z
    (H_apply_ne_zero Γ z)]
  have hH : (H Γ : ℍ → ℂ) z ≠ 0 := H_apply_ne_zero Γ z
  rw [show ((G Γ - c • H Γ : ModularForm _ 12) : ℍ → ℂ) z = (G Γ : ℍ → ℂ) z - c * (H Γ : ℍ → ℂ) z by
    rw [ModularForm.coe_sub, Pi.sub_apply, ModularForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul],
    sub_div, mul_div_cancel_right₀ _ hH, G_apply, coe_H]

end JREG

section Main

variable (M : ℕ) [NeZero M]

theorem order_jqModC' (κ : Type) [Field κ] : (jqModC κ).order = -1 := by
  have hu : (HahnSeries.ofPowerSeries ℤ κ (jNum.map (Int.castRingHom κ))) ≠ 0 := by
    intro h
    have := congrArg (fun x : LaurentSeries κ => x.coeff 0) h
    simp only [HahnSeries.coeff_zero] at this
    rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum] at this
    simp at this
  have hu0 : (HahnSeries.ofPowerSeries ℤ κ (jNum.map (Int.castRingHom κ))).order = 0 := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
      simp
    · rw [HahnSeries.le_order_iff_forall hu]
      intro k hk
      exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk
  rw [jqModC, HahnSeries.order_mul (by simp) hu, hu0, HahnSeries.order_single one_ne_zero, add_zero]

omit [NeZero M] in
theorem T_mem_Gamma1 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem exists_coe_eq_jqModC :
    ∃ y : laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)),
      (y : LaurentSeries ℂ) = jqModC ℂ := by
  obtain ⟨k, A, B, pA, pB, hA, hB, hB0, hjq⟩ := ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 M)
  have hmem : jqModC ℚ ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M) := by
    rw [hjq]
    exact intFormRatiosC_subset ℚ _ (mem_intFormRatiosC A B hA hB hB0)
  refine ⟨⟨coeffEmb ℂ (jqModC ℚ), coeffEmb_mem_laurentBaseChange ℂ hmem⟩, ?_⟩
  show coeffEmb ℂ (jqModC ℚ) = jqModC ℂ
  rw [coeffEmb]
  exact map_jqModC (algebraMap ℚ ℂ)

end Main

end ModularCurve.RamOne
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.ModularCurve.RamOne"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.ModularCurve.RamOne"

open UpperHalfPlane ModularForm ModularGroup _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.ModularCurve ModularCurve.RamOne in
open scoped MatrixGroups Modular in
theorem solution
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
    (D : ModularCurve.ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma1 M) F₀) (τ : UpperHalfPlane) :
    D.ramification τ = 1 := by
  classical
  subst hF
  haveI : Fact (ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M) := ⟨T_mem_Gamma1 M⟩
  obtain ⟨y, hy⟩ := exists_coe_eq_jqModC M
  set c : ℂ := (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ with hc
  set x := y - algebraMap ℂ _ c with hxdef
  have hxcoe : (x : LaurentSeries ℂ) = jqModC ℂ - HahnSeries.C c := by
    rw [hxdef, AddSubgroupClass.coe_sub, hy,
      show ((algebraMap ℂ ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) c :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ) =
        algebraMap ℂ (LaurentSeries ℂ) c from rfl,
      algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 : (jqModC ℂ - HahnSeries.C c).coeff (-1) = 0 := by
      rw [← hxcoe, h0, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
    rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num : (-1 : ℤ) ≠ 0),
      sub_zero] at h1
    have hord := order_jqModC' ℂ
    have hne : jqModC ℂ ≠ 0 := by
      intro h; rw [h, HahnSeries.order_zero] at hord; norm_num at hord
    have := mt HahnSeries.coeff_order_eq_zero.mp hne
    rw [hord] at this
    exact this h1

  have hkey : ((D.ramification τ : ℤ) * (D.pt τ).ord x : ℤ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by
    have h := D.meromorphicOrderAt_realizeOf τ x hx0
    have hfun : (fun z : ℂ => realizeOf (CongruenceSubgroup.Gamma1 M) (x : LaurentSeries ℂ) (ofComplex z)) =
        (fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 / ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) := by
      funext z
      rw [hxcoe, realizeOf_jqModC_sub]
    rw [hfun, ModularCurve.meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two τ] at h
    exact_mod_cast h.symm
  have he : 0 < D.ramification τ := D.ramification_pos τ

  rcases orbit_trichotomy τ with ⟨γ, rfl⟩ | ⟨γ, rfl⟩ | hgen
  ·
    rw [natCard_stabilizer_smul, natCard_stabilizer_I] at hkey
    have hcval : c = 1728 := by
      rw [hc]
      have := jf_eq_of_E₆_eq_zero ((E₆_smul_eq_zero_iff γ _).mpr E₆_I)
      exact this
    have hx' : x = y - 1728 := by
      rw [hxdef, hcval, map_ofNat]
    rw [hx'] at hkey
    have hpos : 0 < (D.pt (γ • UpperHalfPlane.I)).ord (y - 1728) :=
      (mul_pos_iff_of_pos_left (show (0 : ℤ) < D.ramification (γ • UpperHalfPlane.I) by exact_mod_cast he)).mp
        (by rw [hkey]; norm_num)
    have h2 := (ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1 ℂ M hM y hy).2
      _ hpos
    rw [h2] at hkey
    norm_num at hkey
    exact_mod_cast hkey
  ·
    rw [natCard_stabilizer_smul, natCard_stabilizer_ρ] at hkey
    have hcval : c = 0 := by
      have h4 := (E₄_smul_eq_zero_iff γ _).mpr E₄_ρ
      rw [hc, h4, zero_pow three_ne_zero, zero_div]
    have hx' : x = y := by rw [hxdef, hcval, map_zero, sub_zero]
    rw [hx'] at hkey
    have hpos : 0 < (D.pt (γ • ρ)).ord y :=
      (mul_pos_iff_of_pos_left (show (0 : ℤ) < D.ramification (γ • ρ) by exact_mod_cast he)).mp
        (by rw [hkey]; norm_num)
    have h3 := (ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1 ℂ M hM y hy).1
      _ hpos
    rw [h3] at hkey
    norm_num at hkey
    exact_mod_cast hkey
  ·
    rw [natCard_stabilizer_eq_two hgen] at hkey
    norm_num at hkey

    have h1 : (D.ramification τ : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) hkey
    exact_mod_cast h1

#print axioms solution

end S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1 (solution)
