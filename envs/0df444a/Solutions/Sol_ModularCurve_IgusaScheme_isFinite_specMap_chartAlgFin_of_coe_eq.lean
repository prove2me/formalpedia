-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isFinite_specMap_chartAlgFin_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/adc93a2a-ffad-5926-97c9-8433cbf8a523

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.chartAlg IgusaScheme.mem_chartAlg_iff IgusaScheme.adjoin_le_chartAlg IgusaScheme.chartAlgFin IgusaScheme qExpand jq modularFunctionFieldFull jqd_mem_full IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull chartAlg mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin jChartFin coe_jChartFin finiteType_chartAlgFin_and_chartAlgInf qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg"
namespace IotaFin
p2m_open "ModularCurve.IgusaScheme ModularCurve"

private theorem chartAlg_le_chartAlg_of_subset {M q : ℕ} [NeZero M] [Fact q.Prime]
    {S S' : Set ↥(modularFunctionFieldFull M)} (h : S ⊆ (IgusaScheme.chartAlg M q S' : Set ↥(modularFunctionFieldFull M))) :
    IgusaScheme.chartAlg M q S ≤ IgusaScheme.chartAlg M q S' := by
  intro x hx
  let T : Subalgebra ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M) := IgusaScheme.chartAlg M q S'
  let A₂ : Subalgebra ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M) := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) S'
  have hle : Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) S ≤ T := Algebra.adjoin_le h
  have hxT : IsIntegral T x :=
    ((IgusaScheme.mem_chartAlg_iff M q).mp hx).map_of_comp_eq (Subalgebra.inclusion hle).toRingHom
      (RingHom.id _) (by ext; rfl)
  letI : Algebra A₂ T := (Subalgebra.inclusion (IgusaScheme.adjoin_le_chartAlg M q S')).toRingHom.toAlgebra
  haveI : IsScalarTower A₂ T ↥(modularFunctionFieldFull M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A₂ T :=
    ⟨fun t => (isIntegral_algHom_iff (IsScalarTower.toAlgHom A₂ T ↥(modularFunctionFieldFull M))
      Subtype.val_injective).mp ((IgusaScheme.mem_chartAlg_iff M q).mp t.2)⟩
  exact (IgusaScheme.mem_chartAlg_iff M q).mpr (isIntegral_trans x hxT)

private theorem isFinite_specMap_of_le_chartAlg (M M' q : ℕ) [NeZero M] [NeZero M'] [Fact q.Prime]
    (ι : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q))
    (s : ↥(modularFunctionFieldFull M'))
    (hs : ∃ a : ↥(IgusaScheme.chartAlgFin M q),
      ((ι a : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) = s)
    (hle : IgusaScheme.chartAlgFin M' q ≤ IgusaScheme.chartAlg M' q {s}) :
    IsFinite (Spec.map (CommRingCat.ofHom ι.toRingHom)) := by
  obtain ⟨hft, -⟩ := ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf M' q
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  apply RingHom.IsIntegral.to_finite
  · intro x
    obtain ⟨p, hpmon, hpx⟩ :
        IsIntegral ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({s} : Set ↥(modularFunctionFieldFull M'))) (x : ↥(modularFunctionFieldFull M')) :=
      (IgusaScheme.mem_chartAlg_iff M' q).mp (hle x.2)

    let g : ↥(IgusaScheme.chartAlgFin M q) →+* ↥(modularFunctionFieldFull M') :=
      (IgusaScheme.chartAlgFin M' q).val.toRingHom.comp ι.toRingHom
    have hsg : (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({s} : Set ↥(modularFunctionFieldFull M')) : Set ↥(modularFunctionFieldFull M')) ⊆
        Set.range g := by
      have h1 : Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({s} : Set ↥(modularFunctionFieldFull M')) ≤
          ((IgusaScheme.chartAlgFin M' q).val.comp ι).range :=
        Algebra.adjoin_le (by
          rintro _ rfl
          obtain ⟨a, ha⟩ := hs
          exact ⟨a, ha⟩)
      intro y hy
      obtain ⟨a, ha⟩ := (AlgHom.mem_range _).mp (h1 hy)
      exact ⟨a, ha⟩
    have hp'mon : (p.map (algebraMap _ ↥(modularFunctionFieldFull M'))).Monic := hpmon.map _
    have hlifts : p.map (algebraMap _ ↥(modularFunctionFieldFull M')) ∈ Polynomial.lifts g :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => by
        rw [Polynomial.coeff_map]
        exact hsg (p.coeff n).2
    obtain ⟨r, hr, -, hrmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp'mon
    refine ⟨r, hrmon, ?_⟩
    apply Subtype.val_injective
    have h1 : ((Polynomial.eval₂ ι.toRingHom x r : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) =
        Polynomial.eval₂ g (x : ↥(modularFunctionFieldFull M')) r :=
      Polynomial.hom_eval₂ r ι.toRingHom (IgusaScheme.chartAlgFin M' q).val.toRingHom x
    rw [h1, ← Polynomial.eval_map, hr, Polynomial.eval_map, hpx]
    rfl
  · have hc : ι.toRingHom.comp (algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(IgusaScheme.chartAlgFin M q)) =
        algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(IgusaScheme.chartAlgFin M' q) := RingHom.ext fun r => ι.commutes r
    have hft' : (algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(IgusaScheme.chartAlgFin M' q)).FiniteType :=
      RingHom.finiteType_algebraMap.mpr hft
    rw [← hc] at hft'
    exact RingHom.FiniteType.of_comp_finiteType hft'

end ModularCurve.IgusaScheme.IotaFin

open ModularCurve.IgusaScheme.IotaFin in

theorem solution
    (M q ℓ : ℕ) [NeZero M] [Fact q.Prime] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ)
    (ι : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q))
    (e : LaurentSeries ℚ →+* LaurentSeries ℚ) (he : e = RingHom.id _ ∨ e = qExpand ℚ ℓ)
    (hι : ∀ b, (((ι b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        e ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) :
    IsFinite (Spec.map (CommRingCat.ofHom ι.toRingHom)) := by
  rcases he with rfl | rfl
  ·
    refine isFinite_specMap_of_le_chartAlg M M' q ι (jFull M') ⟨jChartFin M q, Subtype.ext ?_⟩ le_rfl
    rw [hι, RingHom.id_apply, coe_jChartFin, coe_jFull, coe_jFull]
  ·
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    have hd : ℓ ∣ M' := hM' ▸ dvd_mul_left ℓ M
    obtain ⟨-, -, h3⟩ := ModularCurve.IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg M' q ℓ hd
    refine isFinite_specMap_of_le_chartAlg M M' q ι ⟨qExpand ℚ ℓ jq, jqd_mem_full M' hd⟩
      ⟨jChartFin M q, Subtype.ext ?_⟩ (chartAlg_le_chartAlg_of_subset (Set.singleton_subset_iff.mpr h3))
    rw [hι, coe_jChartFin, coe_jFull]

end S_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq (solution)
