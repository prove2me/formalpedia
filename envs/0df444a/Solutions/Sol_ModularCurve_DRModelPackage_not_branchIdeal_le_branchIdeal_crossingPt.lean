-- Prove2me | solution 1 for ModularCurve.DRModelPackage.not_branchIdeal_le_branchIdeal_crossingPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a2f3e76c-b167-5a76-b774-0f0e0c99c566

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackage_eq_baseChangeMap_genericPoint_of_specializes
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_not_branchIdeal_le_branchIdeal_crossingPt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_not_branchIdeal_le_branchIdeal_crossingPt.AlgebraicGeometry ModularCurve IsLocalRing"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Spec.map Scheme IsAffineOpen Scheme.branchIdeal"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ basicOpen isBasis_affineOpens Opens le_iff_specializes branchIdeal"
namespace BranchIdeal
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"

universe u

theorem comap_maximalIdeal_eq_map_of_isLocalization_atPrime
    {A Sp Sq : Type*} [CommRing A] [CommRing Sp] [CommRing Sq] [Algebra A Sp] [Algebra A Sq]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime Sp p] [IsLocalization.AtPrime Sq q]
    [IsLocalRing Sq] (φ : Sp →+* Sq) (hφ : ∀ a, φ (algebraMap A Sp a) = algebraMap A Sq a) :
    (maximalIdeal Sq).comap φ = q.map (algebraMap A Sp) := by
  apply le_antisymm
  · intro z hz
    rw [Ideal.mem_comap] at hz
    set a : A := (IsLocalization.sec p.primeCompl z).1
    set s : p.primeCompl := (IsLocalization.sec p.primeCompl z).2
    have hz' : IsLocalization.mk' Sp a s = z := IsLocalization.mk'_sec Sp z
    rw [← hz'] at hz ⊢
    have h1 : IsLocalization.mk' Sp a s * algebraMap A Sp s = algebraMap A Sp a := IsLocalization.mk'_spec Sp a s
    have h2 : φ (IsLocalization.mk' Sp a s) * algebraMap A Sq s = algebraMap A Sq a := by
      rw [← hφ, ← hφ, ← map_mul, h1]
    have ha : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q, ← h2]
      exact Ideal.mul_mem_right _ _ hz
    have hu : IsUnit (algebraMap A Sp s) := IsLocalization.map_units Sp s
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, h1]
    exact Ideal.mem_map_of_mem _ ha
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q a).mpr ha

theorem map_primeIdealOf_eq_branchIdeal {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {a x : X} (h : a ⤳ x)
    (hx : x ∈ U) (ha : a ∈ U) :
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    ((hU.primeIdealOf ⟨a, ha⟩).asIdeal).map (algebraMap Γ(X, U) (X.presheaf.stalk x)) = branchIdeal h := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  letI := X.presheaf.algebra_section_stalk (⟨a, ha⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨a, ha⟩
  symm
  refine comap_maximalIdeal_eq_map_of_isLocalization_atPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (hU.primeIdealOf ⟨a, ha⟩).asIdeal (X.presheaf.stalkSpecializes h).hom (fun s => ?_)
  change (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hx).hom s) = (X.presheaf.germ U a ha).hom s
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

theorem specializes_of_branchIdeal_le {X : Scheme.{u}} {a b x : X} (ha : a ⤳ x) (hb : b ⤳ x)
    (h : branchIdeal hb ≤ branchIdeal ha) : b ⤳ a := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have haU : a ∈ U := ha.mem_open U.isOpen hxU
  have hbU : b ∈ U := hb.mem_open U.isOpen hxU
  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [← map_primeIdealOf_eq_branchIdeal hU ha hxU haU, ← map_primeIdealOf_eq_branchIdeal hU hb hxU hbU] at h

  have hle : ∀ {c : X} (hc : c ⤳ x) (hcU : c ∈ U), hU.primeIdealOf ⟨c, hcU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩ := by
    intro c hc hcU
    have hsp : hU.fromSpec.base (hU.primeIdealOf ⟨c, hcU⟩) ⤳ hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) := by
      rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hc
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp)
  have hdisj : ∀ {c : X} (hc : c ⤳ x) (hcU : c ∈ U),
      Disjoint ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl : Set Γ(X, U)) (hU.primeIdealOf ⟨c, hcU⟩).asIdeal :=
    fun hc hcU => Set.disjoint_left.mpr fun s hs hsQ => hs (hle hc hcU hsQ)
  have ea := IsLocalization.under_map_of_isPrime_disjoint (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (hU.primeIdealOf ⟨a, haU⟩).isPrime (hdisj ha haU)
  have eb := IsLocalization.under_map_of_isPrime_disjoint (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (hU.primeIdealOf ⟨b, hbU⟩).isPrime (hdisj hb hbU)
  have hab : hU.primeIdealOf ⟨b, hbU⟩ ≤ hU.primeIdealOf ⟨a, haU⟩ := by
    change (hU.primeIdealOf ⟨b, hbU⟩).asIdeal ≤ (hU.primeIdealOf ⟨a, haU⟩).asIdeal
    rw [← ea, ← eb]
    exact Ideal.comap_mono h
  have hsp := ((PrimeSpectrum.le_iff_specializes _ _).mp hab).map hU.fromSpec.base.hom.continuous
  rwa [hU.fromSpec_primeIdealOf ⟨b, hbU⟩, hU.fromSpec_primeIdealOf ⟨a, haU⟩] at hsp

end AlgebraicGeometry.Scheme.BranchIdeal

open AlgebraicGeometry.Scheme.BranchIdeal in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    ¬ Scheme.branchIdeal hzero ≤ Scheme.branchIdeal hinf ∧ ¬ Scheme.branchIdeal hinf ≤ Scheme.branchIdeal hzero := by
  have hne := ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
    p 𝔛 O hϖ κ toκ
  have hmax := ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ
  have hVinf : 𝔛.ξinf O κ toκ ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
    ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _
  have hVzero : 𝔛.ξzero O κ toκ ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
    ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _
  constructor
  · intro h

    exact hne (hmax.1 _ hVzero (specializes_of_branchIdeal_le hinf hzero h)).symm
  · intro h
    exact hne (hmax.2 _ hVinf (specializes_of_branchIdeal_le hzero hinf h))

end S_ModularCurve_DRModelPackage_not_branchIdeal_le_branchIdeal_crossingPt
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_not_branchIdeal_le_branchIdeal_crossingPt (solution)
