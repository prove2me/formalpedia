-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_chartAlgFin_comap_eq_of_comap_eq_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4736b733-7c9c-5c18-b84e-21274c0be48c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
import Theorems.Thm_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_chartAlgFin_comap_eq_of_comap_eq_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
    (hιF : ∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L))
    (y y' : ↥(XFin A (↥K) j))
    (hyy' : y'.asIdeal.comap ιF.toRingHom = y.asIdeal.comap ιF.toRingHom) :
    ∃ τ : ↥(chartAlgFin A (↥K) j) ≃ₐ[A] ↥(chartAlgFin A (↥K) j),
      (∀ r : ↥(chartAlgFin A (↥K₁) j₁), τ (ιF r) = ιF r) ∧
      y'.asIdeal = y.asIdeal.comap τ.toAlgHom.toRingHom := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨hrel, hgal, -⟩ :=
    ModularCurve.relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0 p M hM hpM L K hK K₁ hK₁ hle
  haveI : FiniteDimensional ↥K₁ ↥(IntermediateField.extendScalars hle) := by
    apply FiniteDimensional.of_finrank_pos
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hle, hrel]
    have := hp.two_le
    omega
  haveI := hgal
  obtain ⟨G, _iG1, _iG2, _iG3, hGfaith, hGfixK, hGinvK⟩ := IntermediateField.exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars K₁ K hle

  letI algK : Algebra ↥K₁ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have halgK : ∀ x : ↥K₁, ((algebraMap ↥K₁ ↥K x : ↥K) : LaurentSeries L) = (x : LaurentSeries L) := fun _ => rfl
  haveI : IsScalarTower A ↥K₁ ↥K := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    rw [halgK, IsScalarTower.algebraMap_apply A L ↥K a, IsScalarTower.algebraMap_apply A L ↥K₁ a]
    rfl)
  haveI : SMulCommClass G ↥K₁ ↥K := ⟨fun g x y => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hGfixK g _ (by rw [halgK]; exact x.2)]⟩
  haveI : Algebra.IsInvariant ↥K₁ ↥K G := ⟨fun x hx => ⟨⟨(x : LaurentSeries L), hGinvK x hx⟩, Subtype.ext rfl⟩⟩
  have hS : algebraMap ↥K₁ ↥K '' {j₁} = {j} := by
    rw [Set.image_singleton, Set.singleton_eq_singleton_iff]
    exact Subtype.ext (by rw [halgK, hj₁, hj])

  obtain ⟨_iGA, hGA, hGsmulA, hGA₂, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
      A ↥K₁ ↥K G {j₁} {j} hS ιF (fun x => Subtype.ext (hιF x))
  letI algF : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₁) j₁) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ιF.toRingHom.toAlgebra
  obtain ⟨hGsmulF, hGinvF⟩ := hGA₂
  haveI := hGsmulA
  haveI := hGsmulF
  haveI := hGinvF
  haveI : Finite G := Finite.of_fintype G

  have hunder : Ideal.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₁) j₁) y.asIdeal = Ideal.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₁) j₁) y'.asIdeal := by
    rw [Ideal.under_def, Ideal.under_def]
    exact hyy'.symm
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₁) j₁) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) G y.asIdeal y'.asIdeal hunder
  refine ⟨(MulSemiringAction.toAlgEquiv A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) g).symm, fun r => ?_, ?_⟩
  ·
    rw [MulSemiringAction.toAlgEquiv_symm_apply]
    have h := smul_comm g⁻¹ r (1 : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    rw [smul_one, Algebra.smul_def, mul_one] at h
    exact h
  ·
    rw [hg, Ideal.pointwise_smul_eq_comap]
    congr 1

end S_ModularCurve_XOneP_exists_algEquiv_chartAlgFin_comap_eq_of_comap_eq_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_chartAlgFin_comap_eq_of_comap_eq_twoChartIntegralModel_x1_mul (solution)
