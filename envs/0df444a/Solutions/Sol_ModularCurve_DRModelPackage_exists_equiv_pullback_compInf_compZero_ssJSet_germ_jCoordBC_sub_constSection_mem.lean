-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ad140fd7-133b-5d0d-bc3a-1dc38e3b1e6d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
import Theorems.Thm_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
import Theorems.Thm_ModularCurve_DRModel_map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_minimalPrimes_pair_modularUnitSeries
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Theorems.Thm_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

section Unit1

open AlgebraicGeometry CategoryTheory Topology

universe u

private theorem genericPoint_image_specializes {Z X : Scheme.{u}} [IrreducibleSpace Z] (ι : Z ⟶ X)
    {x : X} (hx : x ∈ Set.range ι) : ι (genericPoint Z) ⤳ x := by
  obtain ⟨z, rfl⟩ := hx
  exact (genericPoint_specializes z).map ι.continuous

private theorem asIdeal_le_of_specializes {R : CommRingCat.{u}} {X : Scheme.{u}} (f : Spec R ⟶ X)
    [IsOpenImmersion f] {P Q : PrimeSpectrum R} (h : f P ⤳ f Q) : P.asIdeal ≤ Q.asIdeal :=
  (PrimeSpectrum.le_iff_specializes P Q).mpr (f.isOpenEmbedding.isInducing.specializes_iff.mp h)

end Unit1

section Unit2

open Polynomial TensorProduct

private theorem exists_algebraMap_int_eq (r : ℤ) : ∃ n : ℤ, algebraMap ℤ ℤ n = r :=
  ⟨r, eq_intCast (algebraMap ℤ ℤ) r⟩

private theorem exists_isPrime_and_comap_includeLeft_eq {R : Type*} [CommRing R]
    (hR : ∀ r : R, ∃ n : ℤ, algebraMap ℤ R n = r) {F : Type*} [Field F] [Algebra R F] (S : Subalgebra R F)
    (p : ℕ) [Fact p.Prime] (𝔭 : Ideal S) (e : S ⧸ 𝔭 ≃+* (ZMod p)[X]) (k : Type*) [Field k] [Algebra R k]
    [CharP k p] :
    ∃ 𝔮 : Ideal (S ⊗[R] k), 𝔮.IsPrime ∧
      𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := k)) = 𝔭 := by
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) k) := (ZMod.castHom (dvd_refl p) k).injective
  let φ : S →+* k[X] :=
    (Polynomial.mapRingHom (ZMod.castHom (dvd_refl p) k)).comp (e.toRingHom.comp (Ideal.Quotient.mk 𝔭))
  let φₐ : S →ₐ[R] k[X] :=
    ⟨φ, fun r => by
      obtain ⟨n, rfl⟩ := hR r
      rw [eq_intCast (algebraMap ℤ R) n]
      change φ (algebraMap R S (n : R)) = algebraMap R k[X] (n : R)
      rw [map_intCast (algebraMap R S) n, map_intCast φ n, map_intCast (algebraMap R k[X]) n]⟩
  refine ⟨RingHom.ker (Algebra.TensorProduct.lift φₐ (Polynomial.CAlgHom (R := R) (A := k))
      (fun _ _ => Commute.all _ _)).toRingHom, RingHom.ker_isPrime _, ?_⟩
  ext a
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change Algebra.TensorProduct.lift φₐ _ _ (a ⊗ₜ[R] (1 : k)) = 0 ↔ a ∈ 𝔭
  rw [Algebra.TensorProduct.lift_tmul]
  change φ a * Polynomial.C (1 : k) = 0 ↔ a ∈ 𝔭
  rw [map_one, mul_one]
  change Polynomial.map (ZMod.castHom (dvd_refl p) k) (e (Ideal.Quotient.mk 𝔭 a)) = 0 ↔ a ∈ 𝔭
  rw [Polynomial.map_eq_zero_iff hinj, e.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end Unit2

section Unit3

open TensorProduct

private theorem mem_range_of_specializes_of_mem_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpen (Set.range f)) {a b : Y} (h : a ⤳ b) (hb : b ∈ Set.range f) : a ∈ Set.range f :=
  h.mem_open hf hb

private theorem natCast_tensor_eq_zero {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    (S : Subalgebra R F) (p : ℕ) (k : Type*) [CommRing k] [Algebra R k] [CharP k p] :
    ((p : ℕ) : S ⊗[R] k) = 0 := by
  rw [← map_natCast (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := k)), CharP.cast_eq_zero k p,
    map_zero]

private theorem span_natCast_le_comap_includeLeft {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    (S : Subalgebra R F) (p : ℕ) (k : Type*) [CommRing k] [Algebra R k] [CharP k p] (𝔔 : Ideal (S ⊗[R] k)) :
    Ideal.span {((p : ℕ) : S)} ≤ 𝔔.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := k)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast,
    natCast_tensor_eq_zero]
  exact zero_mem _

end Unit3

section Unit4

set_option autoImplicit false

open Polynomial AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull IgusaScheme.jFull IgusaScheme ssJSet HpoolLevelRing.Afin modularUnitSeries jWidth jWidth_eq_one_or DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap DRModel.map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet HpoolLevelRing.exists_minimalPrimes_pair_modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull ssJSet_finite DRModel.baseChangeMap DRModelPackage.crossingPt_mem_preimage_chartFin DRModelPackage.crossingPt"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "e₀ crossing_card comp_jointly_surjective compInf_isClosedImmersion compZero_isClosedImmersion compZero compInf mk compl_jNeLocus_inter_range_comp_eq_singleton crossingPt_mem_preimage_chartFin crossingPt"
p2m_open "ModularCurve.DRModelPackage ModularCurve"

private theorem exists_mem_and_sub_mem_of_map_quotient_eq_prod
    {R B k : Type*} [CommRing R] [CommRing B] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (𝔭 : Ideal R) (e : (R ⧸ 𝔭) ≃+* (ZMod p)[X]) (j u : R) (hej : e (Ideal.Quotient.mk 𝔭 j) = X)
    (S : Finset k) (n : k → ℕ) (hn : ∀ a ∈ S, 0 < n a)
    (hu : (e (Ideal.Quotient.mk 𝔭 u)).map (ZMod.castHom (dvd_refl p) k) = ∏ a ∈ S, (X - C a) ^ n a)
    (g : R →+* B) (c : k →+* B) (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔭 : 𝔭.map g ≤ 𝔮) (hu𝔮 : g u ∈ 𝔮) :
    ∃ a ∈ S, g j - c a ∈ 𝔮 := by
  classical

  set π : B →+* B ⧸ 𝔮 := Ideal.Quotient.mk 𝔮 with hπ
  have hlift : ∀ r ∈ 𝔭, (π.comp g) r = 0 := fun r hr => by
    simpa [hπ, Ideal.Quotient.eq_zero_iff_mem] using (Ideal.map_le_iff_le_comap.mp h𝔭) hr
  set gbar : R ⧸ 𝔭 →+* B ⧸ 𝔮 := Ideal.Quotient.lift 𝔭 (π.comp g) hlift with hgbar
  set φ : (ZMod p)[X] →+* B ⧸ 𝔮 := gbar.comp e.symm.toRingHom with hφ
  set ξ : B ⧸ 𝔮 := φ X with hξ

  have key : ∀ P : (ZMod p)[X], φ P = (P.map (ZMod.castHom (dvd_refl p) k)).eval₂ (π.comp c) ξ := by
    have h2 : φ = ((Polynomial.eval₂RingHom (π.comp c) ξ).comp
        (Polynomial.mapRingHom (ZMod.castHom (dvd_refl p) k))) := by
      apply Polynomial.ringHom_ext
      · intro a
        have hz : φ.comp Polynomial.C =
            ((Polynomial.eval₂RingHom (π.comp c) ξ).comp
              (Polynomial.mapRingHom (ZMod.castHom (dvd_refl p) k))).comp Polynomial.C :=
          RingHom.ext_zmod _ _
        exact RingHom.congr_fun hz a
      · simp [hξ]
    intro P
    rw [h2]
    simp

  have hu0 : φ (e (Ideal.Quotient.mk 𝔭 u)) = 0 := by
    simp [hφ, hgbar, hπ, Ideal.Quotient.eq_zero_iff_mem, hu𝔮]
  rw [key, hu] at hu0
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at hu0
  obtain ⟨a, ha, ha0⟩ := Finset.prod_eq_zero_iff.mp hu0
  refine ⟨a, ha, ?_⟩
  have hξa : ξ = (π.comp c) a := sub_eq_zero.mp ((pow_eq_zero_iff (hn a ha).ne').mp ha0)

  have hξj : ξ = π (g j) := by
    have hsymm : e.symm X = Ideal.Quotient.mk 𝔭 j := by rw [← hej, RingEquiv.symm_apply_apply]
    simp [hξ, hφ, hgbar, hsymm]
  have : π (g j - c a) = 0 := by
    rw [map_sub, ← hξj, hξa]; simp
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

private theorem exists_minimalPrimes_pair_and_forall_exists_mem_ssJSet_sub_mem
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ P₀ P₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)),
      P₀.IsPrime ∧ P₁.IsPrime ∧ P₀ ≠ P₁ ∧
      (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)))}).minimalPrimes = {P₀, P₁} ∧
      Nonempty ((↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)) ⧸ P₀) ≃+* (ZMod p)[X]) ∧
      Nonempty ((↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)) ⧸ P₁) ≃+* (ZMod p)[X]) ∧
      ∀ (B : Type) [CommRing B] (f : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)) →+* B) (c : k →+* B) (𝔮 : Ideal B),
        𝔮.IsPrime → P₀.map f ≤ 𝔮 → P₁.map f ≤ 𝔮 →
        ∃ a ∈ ssJSet p k,
          f (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) - c a ∈ 𝔮 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hneW, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  obtain ⟨𝔭₀, 𝔭₁, h𝔭₀, -, hmin, hne, ⟨e₀, hej, -⟩, ⟨e₁, -, -⟩⟩ :=
    DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial p jp hjp W₀ W₁ hp₀ hp₁ hneW hgen
      hcomplete ht hres₀ hres₁
  have hW₀ := (DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap p jp hjp W₀ W₁ hp₀ hp₁ hneW
    hgen hcomplete ht).1
  have h𝔭₀mem :
      𝔭₀ ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert _ _
  have h𝔭₁mem :
      𝔭₁ ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)))}).minimalPrimes := by
    rw [hmin]; exact Set.mem_insert_of_mem _ rfl

  have hmem := modularUnitSeries_mem_modularFunctionFieldFull p
  obtain ⟨u, -, Q₀, Q₁, hu_coe, -, -, -, -, hminQ, -, huQ₁, -, -⟩ :=
    HpoolLevelRing.exists_minimalPrimes_pair_modularUnitSeries p hmem
  have hu : ((u : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = modularUnitSeries p := by
    rw [hu_coe]
  have hQ₁mem :
      Q₁ ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)))}).minimalPrimes := by
    have h : Q₁ ∈ (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes := by
      rw [hminQ]; exact Set.mem_insert_of_mem _ rfl
    exact h
  have hQ₁ : Q₁ = 𝔭₀ ∨ Q₁ = 𝔭₁ := by
    rw [hmin] at hQ₁mem
    simpa using hQ₁mem

  set S : Finset k := (ssJSet_finite p k).toFinset with hS_def
  have hS : ∀ a, a ∈ S ↔ a ∈ ssJSet p k := fun a => by simp [hS_def]
  have hprod := DRModel.map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet p hp W₀ hW₀ 𝔭₀ h𝔭₀ e₀
    hej u hu k S hS
  refine ⟨𝔭₀, 𝔭₁, h𝔭₀mem.1.1, h𝔭₁mem.1.1, hne, hmin, ⟨e₀⟩, ⟨e₁⟩, ?_⟩
  intro B _ f c 𝔮 h𝔮 h₀ h₁
  haveI := h𝔮
  have huQ : f u ∈ 𝔮 := by
    rcases hQ₁ with h | h
    · exact h₀ (Ideal.mem_map_of_mem f (h ▸ huQ₁))
    · exact h₁ (Ideal.mem_map_of_mem f (h ▸ huQ₁))
  obtain ⟨a, haS, ha⟩ := exists_mem_and_sub_mem_of_map_quotient_eq_prod p 𝔭₀ e₀ _ u hej S
    (fun a => 12 / jWidth a)
    (fun a _ => by rcases jWidth_eq_one_or a with h | h | h <;> simp [h]) hprod f c 𝔮 h₀ huQ
  exact ⟨a, (hS a).mp haS, ha⟩

end ModularCurve.DRModelPackage

end Unit4

section Unit5

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem.ModularCurve AlgebraicCurve"

universe u

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull IgusaScheme.jFull IgusaScheme ssJSet HpoolLevelRing.Afin modularUnitSeries jWidth jWidth_eq_one_or DRModel.exists_chartAlgFin_valuationSubring_pair_levelP DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap DRModel.map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet HpoolLevelRing.exists_minimalPrimes_pair_modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull ssJSet_finite DRModel.baseChangeMap DRModelPackage.crossingPt_mem_preimage_chartFin DRModelPackage.crossingPt"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "e₀ crossing_card comp_jointly_surjective compInf_isClosedImmersion compZero_isClosedImmersion compZero compInf mk compl_jNeLocus_inter_range_comp_eq_singleton crossingPt_mem_preimage_chartFin crossingPt"
p2m_open "ModularCurve.DRModelPackage ModularCurve"

private theorem not_mem_jNeLocus_of_germ_sub_mem (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F)
    [Fact (j ≠ 0)] (S : Type u) [CommRing S] [Algebra R S] (c : S) (y : ↥(TwoChartIntegralModel.baseChange R F j S))
    (hy : y ∈ TwoChartIntegralModel.chartFinOpenBC R F j S)
    (hm : ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC R F j S)
          y hy).hom
        (TwoChartIntegralModel.jCoordBC R F j S -
          ((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE le_top).op).hom
            (TwoChartIntegralModel.constSection R F j S c)) ∈
      IsLocalRing.maximalIdeal _) :
    y ∉ ((TwoChartIntegralModel.jNeLocus R F j S c : (TwoChartIntegralModel.baseChange R F j S).Opens) :
      Set ↥(TwoChartIntegralModel.baseChange R F j S)) := by
  intro hmem
  have hnu := (IsLocalRing.mem_maximalIdeal _).mp hm
  rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
  ·
    obtain ⟨_, hu⟩ := (Scheme.mem_basicOpen'' _ _ _).mp h
    exact (mem_nonunits_iff.mp hnu) hu
  ·
    obtain ⟨hinf, hu⟩ := (Scheme.mem_basicOpen'' _ _ _).mp h
    have hw : y ∈ TwoChartIntegralModel.chartFinOpenBC R F j S ⊓ TwoChartIntegralModel.chartInfOpenBC R F j S :=
      ⟨hy, hinf⟩

    set gj := ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC R F j S)
      y hy).hom (TwoChartIntegralModel.jCoordBC R F j S) with hgj
    set gi := ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartInfOpenBC R F j S)
      y hinf).hom (TwoChartIntegralModel.jInvCoordBC R F j S) with hgi
    set gc := ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ ⊤ y trivial).hom
      (TwoChartIntegralModel.constSection R F j S c) with hgc
    have hji : gj * gi = 1 := by
      have h1 := congrArg ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ _ y hw).hom
        (TwoChartIntegralModel.res_jCoordBC_mul_res_jInvCoordBC R F j S)
      rw [map_mul, map_one] at h1
      have e1 : ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ _ y hw).hom
          (((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE (inf_le_left :
            TwoChartIntegralModel.chartFinOpenBC R F j S ⊓ TwoChartIntegralModel.chartInfOpenBC R F j S ≤
              TwoChartIntegralModel.chartFinOpenBC R F j S)).op).hom (TwoChartIntegralModel.jCoordBC R F j S)) = gj :=
        (TwoChartIntegralModel.baseChange R F j S).presheaf.germ_res_apply _ y hw _
      have e2 : ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ _ y hw).hom
          (((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE (inf_le_right :
            TwoChartIntegralModel.chartFinOpenBC R F j S ⊓ TwoChartIntegralModel.chartInfOpenBC R F j S ≤
              TwoChartIntegralModel.chartInfOpenBC R F j S)).op).hom (TwoChartIntegralModel.jInvCoordBC R F j S)) =
          gi :=
        (TwoChartIntegralModel.baseChange R F j S).presheaf.germ_res_apply _ y hw _
      rw [← e1, ← e2]
      exact h1
    have hcF : ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC R F j S)
        y hy).hom (((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE le_top).op).hom
          (TwoChartIntegralModel.constSection R F j S c)) = gc :=
      (TwoChartIntegralModel.baseChange R F j S).presheaf.germ_res_apply _ y hy _
    have hcI : ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartInfOpenBC R F j S)
        y hinf).hom (((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE le_top).op).hom
          (TwoChartIntegralModel.constSection R F j S c)) = gc :=
      (TwoChartIntegralModel.baseChange R F j S).presheaf.germ_res_apply _ y hinf _

    have hmF : gj - gc ∈ IsLocalRing.maximalIdeal ((TwoChartIntegralModel.baseChange R F j S).presheaf.stalk y) := by
      rw [map_sub, hcF] at hm
      exact hm
    have hI : ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartInfOpenBC R F j S)
        y hinf).hom (1 - ((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE le_top).op).hom
          (TwoChartIntegralModel.constSection R F j S c) * TwoChartIntegralModel.jInvCoordBC R F j S) =
        gi * (gj - gc) := by
      rw [map_sub, map_one, map_mul, hcI, ← hgi]
      linear_combination (-1 : (TwoChartIntegralModel.baseChange R F j S).presheaf.stalk y) * hji
    have hunit : IsUnit (gi * (gj - gc)) := by
      rw [← hI]
      exact hu
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ gi hmF))) hunit

private theorem exists_equiv_of_forall_exists_germ_jCoordBC_sub_constSection_mem (p : ℕ) [Fact p.Prime] [NeZero p]
    (𝔛 : DRModelPackage p) (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (v : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) → ↥(ssJSet p k))
    (hv :
      ∀ n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)),
      ∃ hy : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈
          TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k,
        ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ
              (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)
              ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
            (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
              ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map
                (homOfLE le_top).op).hom
                (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
                  k (((v n : ↥(ssJSet p k)) : k)))) ∈
          IsLocalRing.maximalIdeal _) :
    ∃ a : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) ≃ ↥(ssJSet p k),
      ∀ n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)),
        ∃ hy : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈
            TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k,
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)
                ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (((a n : ↥(ssJSet p k)) : k)))) ∈
            IsLocalRing.maximalIdeal _ := by
  classical

  have hnot : ∀ n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)),
      (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∉
        ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k
            ((v n : ↥(ssJSet p k)) : k) :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) := by
    intro n
    obtain ⟨hy, hm⟩ := hv n
    exact not_mem_jNeLocus_of_germ_sub_mem ℤ _ _ k _ _ hy hm

  have hinj : Function.Injective v := by
    intro n n' hnn'
    obtain ⟨x, hx⟩ :=
      (𝔛.compl_jNeLocus_inter_range_comp_eq_singleton p k (𝔛.compInf k) (Or.inl rfl)).1 ((v n : ↥(ssJSet p k)) : k)
    have hn' : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n' ∉
        ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k
            ((v n : ↥(ssJSet p k)) : k) :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) := by
      rw [hnn']
      exact hnot n'
    have h1 := (Set.ext_iff.mp hx ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)).mp
      ⟨hnot n, (pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n, by simp⟩
    have h2 := (Set.ext_iff.mp hx ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n')).mp
      ⟨hn', (pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n', by simp⟩
    haveI := 𝔛.compInf_isClosedImmersion k
    haveI := 𝔛.compZero_isClosedImmersion k
    exact (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).isClosedEmbedding.injective
      ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm)

  haveI : Finite ↥(ssJSet p k) := (ssJSet_finite p k).to_subtype
  exact ⟨Equiv.ofBijective v (hinj.bijective_of_nat_card_le (𝔛.crossing_card k).ge), hv⟩

end ModularCurve.DRModelPackage

end Unit5

section Unit6

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

open scoped TensorProduct

namespace CrossChart

universe u

section Generic

private theorem germ_mem_maximalIdeal_iff_not_mem_basicOpen {X : Scheme.{u}} {U : X.Opens} (x : X) (hx : x ∈ U)
    (s : Γ(X, U)) :
    (X.presheaf.germ U x hx).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔ x ∉ X.basicOpen s := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, X.mem_basicOpen s x hx]

private theorem app_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (i : op U' ⟶ op U) (s : Γ(Y, U')) :
    (f.app U).hom ((Y.presheaf.map i).hom s) =
      (X.presheaf.map ((Opens.map f.base).map i.unop).op).hom ((f.app U').hom s) := by
  have h := congrArg (fun ψ => ψ.hom s) (f.naturality i)
  dsimp only at h
  exact h

private theorem map_apply_eq {X : Scheme.{u}} {A B : X.Opens} (i i' : op A ⟶ op B) (t : Γ(X, A)) :
    (X.presheaf.map i).hom t = (X.presheaf.map i').hom t := by
  rw [Subsingleton.elim i i']

private theorem map_map_apply {X : Scheme.{u}} {A B C : X.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op A ⟶ op C) (t : Γ(X, A)) :
    (X.presheaf.map i').hom ((X.presheaf.map i).hom t) = (X.presheaf.map i'').hom t := by
  have h := congrArg (fun ψ => ψ.hom t) (X.presheaf.map_comp i i')
  rw [map_apply_eq i'' (i ≫ i')]
  exact h.symm

private theorem app_top_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (i : op ⊤ ⟶ op U) (s : Γ(Y, ⊤)) :
    (f.app U).hom ((Y.presheaf.map i).hom s) =
      (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op).hom ((f.appTop).hom s) := by
  rw [app_map_apply]
  exact map_apply_eq _ _ _

private theorem comp_app_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) :
    (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) = ((f ≫ g).app U).hom s := rfl

private theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (f.app ⊤).hom ((g.appTop).hom s) = ((f ≫ g).appTop).hom s := rfl

private theorem app_appIso_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens)
    (t : Γ(X, U)) :
    (f.app (f ''ᵁ U)).hom ((f.appIso U).inv.hom t) =
      (X.presheaf.map (eqToHom (f.preimage_image_eq U)).op).hom t := by
  have h := congrArg (fun ψ => ψ.hom t) (Scheme.Hom.appIso_inv_app f U)
  exact h

private theorem appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    ((Spec.map φ).appTop).hom ((Scheme.ΓSpecIso R).inv.hom r) = (Scheme.ΓSpecIso S).inv.hom (φ.hom r) := by
  have h := congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality φ)
  exact h.symm

end Generic

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (S : Type u) [CommRing S] [Algebra R S]

private theorem app_jCoordBC (g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S)) ⟶ baseChange R F j S)
    (hg₁ : g ≫ baseChangeι R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j))
        (B := S))) ≫ ιFin R F j) :
    (g.app (chartFinOpenBC R F j S)).hom (jCoordBC R F j S) =
      ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ chartFinOpenBC R F j S ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).inv.hom
          ((jChartFin R F j : ↥(chartAlgFin R F j)) ⊗ₜ[R] (1 : S))) := by

  rw [jCoordBC, jCoord, TwoChartsAux.f, TwoChartsAux.sF]
  change (g.app (chartFinOpenBC R F j S)).hom
      (((baseChangeι R F j S).app (chartFinOpen R F j)).hom
        (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map
            (homOfLE (chartFinOpen_le_image_top R F j)).op).hom
          (((ιFin R F j).appIso ⊤).inv.hom
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom (jChartFin R F j))))) = _

  rw [comp_app_apply, Scheme.Hom.congr_app hg₁ (chartFinOpen R F j), CommRingCat.hom_comp, RingHom.comp_apply,
    ← comp_app_apply, app_map_apply (ιFin R F j), app_appIso_inv_apply, map_map_apply _ _ ((homOfLE le_top).op),
    app_top_map_apply, appTop_ΓSpecIso_inv, CommRingCat.hom_ofHom, Algebra.TensorProduct.includeLeftRingHom_apply]

  exact map_map_apply _ _ _ _

private theorem app_res_constSection (g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S)) ⟶ baseChange R F j S)
    (hg₂ : g ≫ baseChangeToBase R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j))
        (B := S)).toRingHom))
    (c : S) :
    (g.app (chartFinOpenBC R F j S)).hom
        (((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
          (constSection R F j S c)) =
      ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ chartFinOpenBC R F j S ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).inv.hom
          ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c)) := by
  rw [app_map_apply, constSection]
  change ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).presheaf.map _).hom ((g.app ⊤).hom
      (((baseChangeToBase R F j S).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom c))) = _
  rw [comp_appTop_apply, hg₂, appTop_ΓSpecIso_inv, CommRingCat.hom_ofHom]
  change ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).presheaf.map _).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).inv.hom
        ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c)) = _
  exact map_apply_eq _ _ _

private theorem app_jCoordBC_sub_constSection
    (g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S)) ⟶ baseChange R F j S)
    (hg₁ : g ≫ baseChangeι R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j))
        (B := S))) ≫ ιFin R F j)
    (hg₂ : g ≫ baseChangeToBase R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j))
        (B := S)).toRingHom))
    (c : S) :
    (g.app (chartFinOpenBC R F j S)).hom
        (jCoordBC R F j S -
          ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
            (constSection R F j S c)) =
      ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ chartFinOpenBC R F j S ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).inv.hom
          ((jChartFin R F j : ↥(chartAlgFin R F j)) ⊗ₜ[R] (1 : S) - (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c)) := by
  rw [map_sub, map_sub, map_sub, app_jCoordBC R F j S g hg₁, app_res_constSection R F j S g hg₂ c]

private theorem germ_jCoordBC_sub_constSection_mem_maximalIdeal_iff
    (g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S)) ⟶ baseChange R F j S)
    (hg₁ : g ≫ baseChangeι R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j))
        (B := S))) ≫ ιFin R F j)
    (hg₂ : g ≫ baseChangeToBase R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j))
        (B := S)).toRingHom))
    (q : ↥(Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S)))) (y : ↥(baseChange R F j S)) (hq : g.base q = y)
    (hy : y ∈ chartFinOpenBC R F j S) (c : S) :
    ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) y hy).hom
        (jCoordBC R F j S -
          ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
            (constSection R F j S c)) ∈
      IsLocalRing.maximalIdeal ((baseChange R F j S).presheaf.stalk y) ↔
    (jChartFin R F j : ↥(chartAlgFin R F j)) ⊗ₜ[R] (1 : S) - (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c ∈ q.asIdeal := by
  subst hq
  rw [germ_mem_maximalIdeal_iff_not_mem_basicOpen]
  have h1 : g.base q ∈ (baseChange R F j S).basicOpen (jCoordBC R F j S -
      ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
        (constSection R F j S c)) ↔
      q ∈ g ⁻¹ᵁ (baseChange R F j S).basicOpen (jCoordBC R F j S -
        ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
          (constSection R F j S c)) := Iff.rfl
  have h2 : g ⁻¹ᵁ (baseChange R F j S).basicOpen (jCoordBC R F j S -
        ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
          (constSection R F j S c)) =
      g ⁻¹ᵁ chartFinOpenBC R F j S ⊓
        PrimeSpectrum.basicOpen ((jChartFin R F j : ↥(chartAlgFin R F j)) ⊗ₜ[R] (1 : S) -
          (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c) := by
    rw [Scheme.preimage_basicOpen]
    change (Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).basicOpen ((g.app (chartFinOpenBC R F j S)).hom
      (jCoordBC R F j S - ((baseChange R F j S).presheaf.map
        (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom (constSection R F j S c))) = _
    rw [app_jCoordBC_sub_constSection R F j S g hg₁ hg₂ c]
    change (Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).basicOpen
      (((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ chartFinOpenBC R F j S ≤ ⊤)).op)
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S))).inv
          ((jChartFin R F j : ↥(chartAlgFin R F j)) ⊗ₜ[R] (1 : S) - (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c))) = _
    rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
  rw [h1, h2]
  change ¬ (g.base q ∈ chartFinOpenBC R F j S ∧ (jChartFin R F j : ↥(chartAlgFin R F j)) ⊗ₜ[R] (1 : S) -
      (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c ∉ q.asIdeal) ↔ _
  constructor
  · intro h
    by_contra hb
    exact h ⟨hy, hb⟩
  · intro hb h
    exact h.2 hb

private theorem exists_germ_jCoordBC_sub_constSection_mem_maximalIdeal
    (g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] S)) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    [IsOpenImmersion g]
    (hg₁ : g ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j))
        (B := S))) ≫ ιFin R F j)
    (hg₂ : g ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j))
        (B := S)).toRingHom))
    (𝔔 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] S)) (c : S)
    (h : jChartFin R F j ⊗ₜ[R] (1 : S) - (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] c ∈ 𝔔.asIdeal) :
    ∃ hy : g.base 𝔔 ∈ TwoChartIntegralModel.chartFinOpenBC R F j S,
      ((TwoChartIntegralModel.baseChange R F j S).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC R F j S)
          (g.base 𝔔) hy).hom
          (TwoChartIntegralModel.jCoordBC R F j S -
            ((TwoChartIntegralModel.baseChange R F j S).presheaf.map (homOfLE le_top).op).hom
              (TwoChartIntegralModel.constSection R F j S c)) ∈
        IsLocalRing.maximalIdeal _ := by
  have hg₁' : g ≫ baseChangeι R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j))
        (B := S))) ≫ ιFin R F j := hg₁
  have hg₂' : g ≫ baseChangeToBase R F j S =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j))
        (B := S)).toRingHom) := hg₂
  have hy : g.base 𝔔 ∈ chartFinOpenBC R F j S := by
    change (g ≫ baseChangeι R F j S).base 𝔔 ∈ Set.range (ιFin R F j).base
    rw [hg₁']
    exact ⟨_, rfl⟩
  exact ⟨hy, (germ_jCoordBC_sub_constSection_mem_maximalIdeal_iff R F j S g hg₁' hg₂' 𝔔 (g.base 𝔔) rfl hy c).mpr h⟩

end CrossChart

end Unit6

section Unit7

set_option autoImplicit false

namespace CrossChair

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem.ModularCurve"

private theorem baseChangeMap_comp_fst {p : ℕ} [Fact p.Prime] {O κ : Type} [CommRing O] [CommRing κ]
    (toκ : O →+* κ) :
    DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [DRModel.baseChangeMap]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem map_le_of_mem_minimalPrimes {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {I P : Ideal A} (hP : P ∈ I.minimalPrimes) (𝔮 𝔔' 𝔔 : Ideal B) [𝔔'.IsPrime]
    (h𝔮 : 𝔮.comap f = P) (hI : I ≤ 𝔔'.comap f) (h₁ : 𝔔' ≤ 𝔔) (h₂ : 𝔔' ≤ 𝔮) : P.map f ≤ 𝔔 := by
  have hPmin : Minimal (fun q : Ideal A => q.IsPrime ∧ I ≤ q) P := hP
  have hQ : 𝔔'.comap f = P :=
    Minimal.eq_of_le hPmin ⟨inferInstance, hI⟩ (h𝔮 ▸ Ideal.comap_mono h₂)
  exact (Ideal.map_le_iff_le_comap.mpr hQ.ge).trans h₁

private theorem map_le_asIdeal_of_mem_range_or {A : Type*} [CommRing A] {B : CommRingCat} {X Z₁ Z₂ : Scheme}
    [IrreducibleSpace Z₁] [IrreducibleSpace Z₂] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) (g : Spec B ⟶ X) [IsOpenImmersion g]
    (f : A →+* B) {I P : Ideal A} (hP : P ∈ I.minimalPrimes) (𝔮 : Ideal B) (h𝔮 : 𝔮.IsPrime) (h𝔮c : 𝔮.comap f = P)
    (𝔔 𝔔₁ 𝔔₂ : ↥(Spec B)) (hI₁ : I ≤ 𝔔₁.asIdeal.comap f) (hI₂ : I ≤ 𝔔₂.asIdeal.comap f)
    (hle₁ : 𝔔₁.asIdeal ≤ 𝔔.asIdeal) (hle₂ : 𝔔₂.asIdeal ≤ 𝔔.asIdeal)
    (h𝔔₁ : g.base 𝔔₁ = i₁.base (genericPoint Z₁)) (h𝔔₂ : g.base 𝔔₂ = i₂.base (genericPoint Z₂))
    (hz : g.base ⟨𝔮, h𝔮⟩ ∈ Set.range i₁.base ∨ g.base ⟨𝔮, h𝔮⟩ ∈ Set.range i₂.base) :
    P.map f ≤ 𝔔.asIdeal := by
  rcases hz with hz | hz
  · exact map_le_of_mem_minimalPrimes f hP 𝔮 𝔔₁.asIdeal 𝔔.asIdeal h𝔮c hI₁ hle₁
      (asIdeal_le_of_specializes g (P := 𝔔₁) (Q := ⟨𝔮, h𝔮⟩)
        (by rw [h𝔔₁]; exact genericPoint_image_specializes i₁ hz))
  · exact map_le_of_mem_minimalPrimes f hP 𝔮 𝔔₂.asIdeal 𝔔.asIdeal h𝔮c hI₂ hle₂
      (asIdeal_le_of_specializes g (P := 𝔔₂) (Q := ⟨𝔮, h𝔮⟩)
        (by rw [h𝔔₂]; exact genericPoint_image_specializes i₂ hz))

end CrossChair

end Unit7

section Main

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem.ModularCurve AlgebraicCurve"
open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ a : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) ≃ ↥(ssJSet p k),
      ∀ n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)),
        ∃ hy : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈
            TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k,
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)
                ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (((a n : ↥(ssJSet p k)) : k)))) ∈
            IsLocalRing.maximalIdeal _ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := 𝔛.compInf_isClosedImmersion k
  haveI := 𝔛.compZero_isClosedImmersion k

  obtain ⟨g, hgo, hg₁, hg₂, hgr⟩ :=
    TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p) k
  haveI := hgo

  obtain ⟨P₀, P₁, _, _, _, hmin, ⟨e₀⟩, ⟨e₁⟩, hval⟩ :=
    DRModelPackage.exists_minimalPrimes_pair_and_forall_exists_mem_ssJSet_sub_mem p hp k
  have key : ∀ n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)), ∃ a : ↥(ssJSet p k),
        ∃ hy : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈
            TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k,
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)
                ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
                      k).presheaf.map (homOfLE le_top).op).hom
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k
                    ((a : ↥(ssJSet p k)) : k))) ∈
            IsLocalRing.maximalIdeal _ := by
    intro n

    have hyU : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈ Set.range g.base := by
      rw [hgr]
      have h := ModularCurve.DRModelPackage.crossingPt_mem_preimage_chartFin p hp 𝔛 k k (RingHom.id k) n
      have e0 : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap (RingHom.id k)) ≫
            pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) =
          (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k) ≫
            pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) := by
        simp only [Category.assoc, CrossChair.baseChangeMap_comp_fst]
      have e1 : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base
            (𝔛.crossingPt k k (RingHom.id k) n) =
          (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base
            ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) := by
        have e2 := congrArg (fun φ => φ.base n) e0
        simpa only [DRModelPackage.crossingPt, Scheme.Hom.comp_base, TopCat.comp_app] using e2
      have h' : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base
            ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) ∈
          TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ''ᵁ ⊤ := by
        rw [← e1]
        exact h
      exact h'
    obtain ⟨𝔔, h𝔔⟩ := hyU

    have hy₁ : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈ Set.range (𝔛.compInf k).base :=
      ⟨(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n, by simp only [Scheme.Hom.comp_base, TopCat.comp_app]⟩
    have hy₂ : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈ Set.range (𝔛.compZero k).base :=
      ⟨(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n, by
        rw [pullback.condition]; simp only [Scheme.Hom.comp_base, TopCat.comp_app]⟩
    have hsp₁ := genericPoint_image_specializes (𝔛.compInf k) hy₁
    have hsp₂ := genericPoint_image_specializes (𝔛.compZero k) hy₂
    obtain ⟨𝔔₁, h𝔔₁⟩ :=
      mem_range_of_specializes_of_mem_range (IsOpenImmersion.isOpen_range g) hsp₁ ⟨𝔔, h𝔔⟩
    obtain ⟨𝔔₂, h𝔔₂⟩ :=
      mem_range_of_specializes_of_mem_range (IsOpenImmersion.isOpen_range g) hsp₂ ⟨𝔔, h𝔔⟩
    have hle₁ : 𝔔₁.asIdeal ≤ 𝔔.asIdeal :=
      asIdeal_le_of_specializes g (by rw [h𝔔₁, h𝔔]; exact hsp₁)
    have hle₂ : 𝔔₂.asIdeal ≤ 𝔔.asIdeal :=
      asIdeal_le_of_specializes g (by rw [h𝔔₂, h𝔔]; exact hsp₂)

    have hP₀m := (Set.ext_iff.mp hmin P₀).mpr (Set.mem_insert _ _)
    have hP₁m := (Set.ext_iff.mp hmin P₁).mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨𝔮₀, h𝔮₀p, h𝔮₀c⟩ := exists_isPrime_and_comap_includeLeft_eq exists_algebraMap_int_eq _ p P₀ e₀ k
    obtain ⟨𝔮₁, h𝔮₁p, h𝔮₁c⟩ := exists_isPrime_and_comap_includeLeft_eq exists_algebraMap_int_eq _ p P₁ e₁ k
    have hI₁ := span_natCast_le_comap_includeLeft _ p k 𝔔₁.asIdeal
    have hI₂ := span_natCast_le_comap_includeLeft _ p k 𝔔₂.asIdeal
    have hP₀ := CrossChair.map_le_asIdeal_of_mem_range_or (𝔛.compInf k) (𝔛.compZero k) g
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
        (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := k))
      hP₀m 𝔮₀ h𝔮₀p h𝔮₀c 𝔔 𝔔₁ 𝔔₂ hI₁ hI₂ hle₁ hle₂ h𝔔₁ h𝔔₂
      (𝔛.comp_jointly_surjective k (g.base ⟨𝔮₀, h𝔮₀p⟩))
    have hP₁ := CrossChair.map_le_asIdeal_of_mem_range_or (𝔛.compInf k) (𝔛.compZero k) g
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
        (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := k))
      hP₁m 𝔮₁ h𝔮₁p h𝔮₁c 𝔔 𝔔₁ 𝔔₂ hI₁ hI₂ hle₁ hle₂ h𝔔₁ h𝔔₂
      (𝔛.comp_jointly_surjective k (g.base ⟨𝔮₁, h𝔮₁p⟩))

    obtain ⟨a, ha, hja⟩ := hval _
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
          (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := k))
      (Algebra.TensorProduct.includeRight (R := ℤ)
        (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
        (B := k)).toRingHom
      𝔔.asIdeal 𝔔.isPrime hP₀ hP₁

    have H := CrossChart.exists_germ_jCoordBC_sub_constSection_mem_maximalIdeal ℤ
      ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k g hg₁ hg₂ 𝔔 a hja
    rw [h𝔔] at H
    exact ⟨⟨a, ha⟩, H⟩
  choose v hv using key
  exact DRModelPackage.exists_equiv_of_forall_exists_germ_jCoordBC_sub_constSection_mem p 𝔛 k v hv

end Main

end S_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem (solution)
