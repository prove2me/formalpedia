-- Prove2me | solution 1 for ModularCurve.finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/468461d5-b63e-52e6-bea4-226e3e4ef9df

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "Period.parabolicHoms Period.mem_parabolicHoms_iff finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup"
namespace Ws49
namespace RankR
p2m_open "ModularCurve"

section Quot

variable {Γ : Type*} [Group Γ] (P : Set Γ)

abbrev Q : Type _ := Abelianization (Γ ⧸ Subgroup.normalClosure P)

def π : Γ →* Q P := Abelianization.of.comp (QuotientGroup.mk' (Subgroup.normalClosure P))

theorem π_apply_of_mem {s : Γ} (hs : s ∈ P) : π P s = 1 := by
  simp only [π, MonoidHom.coe_comp, Function.comp_apply]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff s).mpr (Subgroup.subset_normalClosure hs),
    map_one]

theorem π_surjective : Function.Surjective (π P) :=
  (QuotientGroup.mk_surjective.comp (QuotientGroup.mk'_surjective _))

scoped instance fg_Q [Group.FG Γ] : Group.FG (Q P) := Group.fg_of_surjective (π_surjective P)

scoped instance addFG_Q [Group.FG Γ] : AddGroup.FG (Additive (Q P)) := inferInstance

def mulChar {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R) : Γ →* Multiplicative R :=
  MonoidHom.toAdditiveLeft.symm φ

@[scoped simp] theorem mulChar_apply {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R) (γ : Γ) :
    mulChar φ γ = Multiplicative.ofAdd (φ (Additive.ofMul γ)) := rfl

theorem normalClosure_le_ker {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) : Subgroup.normalClosure P ≤ (mulChar φ).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  intro s hs
  rw [SetLike.mem_coe, MonoidHom.mem_ker, mulChar_apply, hφ s hs]
  rfl

def liftHom {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) : Additive (Q P) →+ R :=
  MonoidHom.toAdditiveLeft
    (Abelianization.lift (QuotientGroup.lift _ (mulChar φ) (normalClosure_le_ker P φ hφ)))

theorem liftHom_π {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) (γ : Γ) :
    liftHom P φ hφ (Additive.ofMul (π P γ)) = φ (Additive.ofMul γ) := by
  unfold liftHom π
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  show Multiplicative.toAdd ((Abelianization.lift _) (Abelianization.of _)) = _
  rw [Abelianization.lift_apply_of, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  rfl

def pullHom {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) : Additive Γ →+ R :=
  ψ.comp (MonoidHom.toAdditive (π P))

@[scoped simp] theorem pullHom_apply {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) (γ : Γ) :
    pullHom P ψ (Additive.ofMul γ) = ψ (Additive.ofMul (π P γ)) := rfl

theorem pullHom_apply' {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) (x : Additive Γ) :
    pullHom P ψ x = ψ (Additive.ofMul (π P (Additive.toMul x))) := rfl

theorem pullHom_apply_of_mem {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) {s : Γ}
    (hs : s ∈ P) : pullHom P ψ (Additive.ofMul s) = 0 := by
  rw [pullHom_apply, π_apply_of_mem P hs, ofMul_one, map_zero]

theorem pullHom_liftHom {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) : pullHom P (liftHom P φ hφ) = φ :=
  AddMonoidHom.ext fun γ => liftHom_π P φ hφ (Additive.toMul γ)

theorem liftHom_pullHom {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) :
    liftHom P (pullHom P ψ) (fun s hs => pullHom_apply_of_mem P ψ hs) = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ, hγ⟩ := π_surjective P (Additive.toMul x)
  have hx : x = Additive.ofMul (π P γ) := by rw [hγ]; rfl
  rw [hx, liftHom_π, pullHom_apply]

theorem pullHom_injective {R : Type*} [AddCommGroup R] :
    Function.Injective (pullHom P (R := R)) := fun a b h => by
  rw [← liftHom_pullHom P a, ← liftHom_pullHom P b]
  simp only [h]

end Quot

end ModularCurve.Ws49.RankR
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49"
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"

noncomputable section

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "Period.parabolicHoms Period.mem_parabolicHoms_iff finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup"
namespace Ws49
namespace RankR
p2m_open "ModularCurve"

section Char

variable {A : Type*} [AddCommGroup A]
variable (R : Type*) [CommRing R] [IsAddTorsionFree R]

theorem hom_eq_zero_of_finite {T : Type*} [AddCommGroup T] [Finite T] (f : T →+ R) : f = 0 := by
  ext t
  have hn : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have h : (Nat.card T) • f t = 0 := by
    rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
  rw [AddMonoidHom.zero_apply]
  exact (IsAddTorsionFree.nsmul_right_injective hn) (by simpa using h)

variable {R}

def evalAt {ι : Type*} (a : ι → A) : (A →+ R) →ₗ[R] (ι → R) where
  toFun f i := f (a i)
  map_add' f g := by funext i; rfl
  map_smul' c f := by funext i; simp

@[scoped simp] theorem evalAt_apply {ι : Type*} (a : ι → A) (f : A →+ R) (i : ι) : evalAt a f i = f (a i) := rfl

def charEquiv {n : ℕ} {T : Type*} [AddCommGroup T] [Finite T] (e : A ≃+ (Fin n →₀ ℤ) × T) :
    (A →+ R) ≃ₗ[R] (Fin n → R) := by
  refine LinearEquiv.ofBijective (evalAt fun i => e.symm (Finsupp.single i 1, 0)) ⟨?_, ?_⟩
  ·
    intro f g hfg
    have key : ∀ h : A →+ R, (∀ i, h (e.symm (Finsupp.single i 1, 0)) = 0) → h = 0 := by
      intro h hh

      have hT : (h.comp e.symm.toAddMonoidHom).comp (AddMonoidHom.inr (Fin n →₀ ℤ) T) = 0 :=
        hom_eq_zero_of_finite R _
      have hZ : (h.comp e.symm.toAddMonoidHom).comp (AddMonoidHom.inl (Fin n →₀ ℤ) T) = 0 := by
        apply Finsupp.addHom_ext
        intro i m
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
          AddMonoidHom.zero_apply]
        have : (Finsupp.single i m, (0 : T)) = m • (Finsupp.single i (1 : ℤ), (0 : T)) := by
          rw [Prod.smul_mk, smul_zero, Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [this, AddEquiv.coe_toAddMonoidHom, map_zsmul, map_zsmul, hh i, smul_zero]
      have hsum : h.comp e.symm.toAddMonoidHom = 0 := by
        ext ⟨x, t⟩
        have : ((x, t) : (Fin n →₀ ℤ) × T) = AddMonoidHom.inl _ _ x + AddMonoidHom.inr _ _ t := by simp
        rw [this, map_add, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, hZ, hT]
        simp
      ext a
      have := congrArg (fun φ : (Fin n →₀ ℤ) × T →+ R => φ (e a)) hsum
      simpa using this
    have h0 := key (f - g) (fun i => by
      have := congrFun hfg i
      simp only [evalAt_apply] at this
      simp [this])
    exact sub_eq_zero.mp h0
  ·
    intro c
    let ψZ : (Fin n →₀ ℤ) →+ R := Finsupp.liftAddHom fun i => (zmultiplesHom R (c i) : ℤ →+ R)
    let ψ : (Fin n →₀ ℤ) × T →+ R := ψZ.comp (AddMonoidHom.fst _ _)
    refine ⟨ψ.comp e.toAddMonoidHom, ?_⟩
    funext i
    simp [ψ, ψZ, evalAt_apply]

theorem finrank_char_eq {n : ℕ} {T : Type*} [AddCommGroup T] [Finite T] (e : A ≃+ (Fin n →₀ ℤ) × T)
    [StrongRankCondition R] : Module.finrank R (A →+ R) = n := by
  rw [(charEquiv (R := R) e).finrank_eq, Module.finrank_fin_fun]

end Char
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"

section Vanishing

variable {Γ : Type*} [Group Γ] (P : Set Γ)
variable (R : Type*) [CommRing R]

def vanishing : Submodule R (Additive Γ →+ R) where
  carrier := {φ | ∀ s ∈ P, φ (Additive.ofMul s) = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ s hs
    show φ _ + ψ _ = 0
    rw [hφ s hs, hψ s hs, add_zero]
  smul_mem' := by
    intro c φ hφ s hs
    show c • φ _ = 0
    rw [hφ s hs, smul_zero]

variable {P R}

theorem mem_vanishing_iff {φ : Additive Γ →+ R} : φ ∈ vanishing P R ↔ ∀ s ∈ P, φ (Additive.ofMul s) = 0 :=
  Iff.rfl

variable (P R)

def vanishingEquiv : vanishing P R ≃ₗ[R] (Additive (Q P) →+ R) where
  toFun φ := liftHom P φ.1 φ.2
  invFun ψ := ⟨pullHom P ψ, fun s hs => pullHom_apply_of_mem P ψ hs⟩
  left_inv φ := Subtype.ext (pullHom_liftHom P φ.1 φ.2)
  right_inv ψ := liftHom_pullHom P ψ
  map_add' φ ψ := by
    apply pullHom_injective P
    rw [pullHom_liftHom]
    refine AddMonoidHom.ext fun γ => ?_
    rw [pullHom_apply', AddMonoidHom.add_apply, liftHom_π, liftHom_π]
    rfl
  map_smul' c φ := by
    apply pullHom_injective P
    rw [pullHom_liftHom]
    refine AddMonoidHom.ext fun γ => ?_
    rw [RingHom.id_apply, pullHom_apply', AddMonoidHom.smul_apply, liftHom_π]
    rfl

theorem exists_forall_finrank_vanishing_eq [Group.FG Γ] :
    ∃ r : ℕ, ∀ (R : Type) [CommRing R] [IsAddTorsionFree R] [StrongRankCondition R],
      Module.finrank R (vanishing P R) = r := by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive (Q P))
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) := by
    classical
    haveI : ∀ i, Fintype (ZMod (p i ^ e i)) := fun i => ZMod.fintype _
    exact Finite.of_equiv (Π₀ i, ZMod (p i ^ e i)) (Equiv.refl _)
  refine ⟨n, fun R _ _ _ => ?_⟩
  rw [(vanishingEquiv P R).finrank_eq]
  exact finrank_char_eq f

end Vanishing
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"

section Parabolic

variable (Γ : Subgroup SL(2, ℤ))

def parabolicSet : Set Γ := {γ | ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4}

theorem parabolicHoms_eq_vanishing (R : Type*) [CommRing R] :
    ModularCurve.Period.parabolicHoms R Γ R = vanishing (parabolicSet Γ) R := by
  ext φ
  rw [ModularCurve.Period.mem_parabolicHoms_iff, mem_vanishing_iff]
  rfl

scoped instance fg_SL2Z : Group.FG SL(2, ℤ) := by
  rw [Group.fg_iff]
  exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance fg_of_finiteIndex [Γ.FiniteIndex] : Group.FG Γ := inferInstance

theorem finrank_real_parabolicHoms_eq_finrank_int [Γ.FiniteIndex] :
    Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) =
      Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) := by
  obtain ⟨r, hr⟩ := exists_forall_finrank_vanishing_eq (parabolicSet Γ)
  rw [parabolicHoms_eq_vanishing, parabolicHoms_eq_vanishing, hr ℝ, hr ℤ]

end Parabolic
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"

end ModularCurve.Ws49.RankR
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"

end
p2m_reactivate "P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR"

open scoped MatrixGroups in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by
  haveI : Γ.FiniteIndex := hΓ.finiteIndex
  rw [ModularCurve.Ws49.RankR.finrank_real_parabolicHoms_eq_finrank_int]
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Γ hΓ

end S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
end P2MW
export P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup (solution)
