-- Prove2me | solution 1 for ModularCurve.IgusaScheme.geometricallyConnected_toBase_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5fe93f93-8e0a-545c-8a27-9f1fb380a61d

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull IgusaScheme.connectedSpace_pullback_igusaTo_specMap IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull igusaTo connectedSpace_pullback_igusaTo_specMap geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo"
namespace GCAllAux
p2m_open "ModularCurve.IgusaScheme ModularCurve"

theorem geometricallyConnected_igusaTo (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    GeometricallyConnected (igusaTo N ℓ) := by
  refine (geometricallyConnected_iff _).mpr ?_
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI : ConnectedSpace ↥(pullback (igusaTo N ℓ)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt ℓ) K)) :=
    ModularCurve.IgusaScheme.connectedSpace_pullback_igusaTo_specMap N ℓ K

  let e := h.isoPullback
  have hsurj : Function.Surjective e.inv.base := e.inv.homeomorph.surjective
  refine connectedSpace_iff_univ.mpr ?_
  rw [← hsurj.range_eq, ← Set.image_univ]
  exact isConnected_univ.image _ e.inv.homeomorph.continuous.continuousOn

theorem geometricallyConnected_pullback_snd_igusaTo (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [CommRing K] (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* K) :
    GeometricallyConnected (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by
  haveI := geometricallyConnected_igusaTo N ℓ
  infer_instance

end ModularCurve.IgusaScheme.GCAllAux

namespace ModularCurve p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull IgusaScheme.connectedSpace_pullback_igusaTo_specMap IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo" namespace IgusaScheme p2m_export "ModularCurve.IgusaScheme" "jFull igusaTo connectedSpace_pullback_igusaTo_specMap geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo" namespace GCAllAux end ModularCurve.IgusaScheme.GCAllAux
p2m_open_scoped "ModularCurve ModularCurve.IgusaScheme" in

theorem ModularCurve.IgusaScheme.GCAllAux.geometricallyConnected_pullback_snd_toBase_int'
    (N : ℕ) [NeZero N] (K : Type) [Field K] [Algebra ℤ K] :
    GeometricallyConnected
      (pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := by

  obtain rfl : ‹Algebra ℤ K› = Ring.toIntAlgebra K := Subsingleton.elim _ _
  obtain ⟨q, hq⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K q with hprime | rfl
  ·
    haveI : Fact q.Prime := ⟨hprime⟩
    haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
      have hq' : Prime (q : ℤ) := by
        rw [Int.prime_iff_natAbs_prime]
        simpa using (Fact.out : q.Prime)
      exact (Ideal.span_singleton_prime hq'.ne_zero).mpr hq'
    haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
    let ψ : ↥(GaloisRep.ratLocalizedAt q) →+* ZMod q :=
      IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl)
        (S := ↥(GaloisRep.ratLocalizedAt q)) (g := Int.castRingHom (ZMod q))
        (fun y => by
          refine isUnit_iff_ne_zero.mpr ?_
          simp only [Int.coe_castRingHom, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro hy
          exact y.2 (Ideal.mem_span_singleton.mpr (by exact_mod_cast hy)))
    exact ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
      N q K ((ZMod.castHom (dvd_refl q) K).comp ψ)
      (ModularCurve.IgusaScheme.GCAllAux.geometricallyConnected_pullback_snd_igusaTo N q K _)
  ·
    haveI : CharZero K := CharP.charP_to_charZero K
    haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    exact ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
      N 2 K ((algebraMap ℚ K).comp (GaloisRep.ratLocalizedAt 2).subtype)
      (ModularCurve.IgusaScheme.GCAllAux.geometricallyConnected_pullback_snd_igusaTo N 2 K _)

theorem solution (N : ℕ) [NeZero N] :
    GeometricallyConnected
      (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N)) := by
  refine (geometricallyConnected_iff _).mpr ?_
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI := ModularCurve.IgusaScheme.GCAllAux.geometricallyConnected_pullback_snd_toBase_int' N K
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  haveI : ConnectedSpace ↥(pullback
      (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))

  let e := h.isoPullback
  have hsurj : Function.Surjective e.inv.base := e.inv.homeomorph.surjective
  refine connectedSpace_iff_univ.mpr ?_
  rw [← hsurj.range_eq, ← Set.image_univ]
  exact isConnected_univ.image _ e.inv.homeomorph.continuous.continuousOn

end S_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int (solution)
