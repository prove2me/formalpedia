-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/45efc295-549b-52f6-ae44-ed0748fc0767

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_ModularCurve_IgusaScheme_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty
import Theorems.Thm_AlgebraicGeometry_exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList
import Theorems.Thm_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve ModularCurve.IgusaScheme
p2m_open "Polynomial AlgebraicGeometry.Polynomial"

namespace IgusaCuspSmooth

noncomputable def affTo (p : ℕ) : Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X]) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (↥(GaloisRep.ratLocalizedAt p))[X]))

theorem smooth_affTo (p : ℕ) : Smooth (affTo p) := by
  rw [affTo, HasRingHomProperty.Spec_iff (P := @Smooth)]
  show RingHom.Smooth (algebraMap ↥(GaloisRep.ratLocalizedAt p) (↥(GaloisRep.ratLocalizedAt p))[X])
  rw [RingHom.smooth_algebraMap]
  exact ⟨inferInstance, inferInstance⟩

variable (M p : ℕ) [NeZero M] [Fact p.Prime]

noncomputable def phi : (↥(GaloisRep.ratLocalizedAt p))[X] →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgInf M p) :=
  Polynomial.aeval (jInvChartInf M p)

noncomputable def g : Spec (CommRingCat.of ↥(chartAlgInf M p)) ⟶ Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X]) :=
  Spec.map (CommRingCat.ofHom (phi M p).toRingHom)

theorem g_affTo : g M p ≫ affTo p = ιInf M p ≫ igusaTo M p := by
  rw [ιInf_igusaTo, g, affTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_algebraMap]

def IsCuspPrime (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) : Prop :=
  ∀ b : ↥(chartAlgInf M p), b ∈ u.asIdeal ↔
    ∃ c ∈ GaloisRep.ratLocalizedAt p, ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c

namespace Stalk

section Aux

set_option linter.unusedSectionVars false

open IsLocalRing

@[reducible] noncomputable def algStalkB (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) :
    Algebra ↥(chartAlgInf M p) ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) :=
  StructureSheaf.stalkAlgebra (R := ↥(chartAlgInf M p)) u

@[reducible] noncomputable def algStalkP (v : Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])) :
    Algebra (↥(GaloisRep.ratLocalizedAt p))[X] ((Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])).presheaf.stalk v) :=
  StructureSheaf.stalkAlgebra (R := (↥(GaloisRep.ratLocalizedAt p))[X]) v

attribute [local instance] algStalkB algStalkP

theorem isLocalization_stalkB (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) :
    IsLocalization.AtPrime ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) u.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk ↥(chartAlgInf M p) u

theorem isLocalization_stalkP (v : Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])) :
    IsLocalization.AtPrime ((Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])).presheaf.stalk v) v.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (↥(GaloisRep.ratLocalizedAt p))[X] v

attribute [local instance] isLocalization_stalkB isLocalization_stalkP

theorem algebraMap_stalkB (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (b : ↥(chartAlgInf M p)) :
    algebraMap ↥(chartAlgInf M p) ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) b =
      StructureSheaf.toStalk ↥(chartAlgInf M p) u b := rfl

theorem algebraMap_stalkP (v : Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])) (r : (↥(GaloisRep.ratLocalizedAt p))[X]) :
    algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] ((Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])).presheaf.stalk v) r =
      StructureSheaf.toStalk (↥(GaloisRep.ratLocalizedAt p))[X] v r := rfl

theorem single_mul_jq : HahnSeries.single (1 : ℤ) (1 : ℚ) * jq = ((jNumQ : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [jq, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

theorem coeff_zero_coe_powerSeries (F : PowerSeries ℚ) :
    (F : LaurentSeries ℚ).coeff 0 = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]

theorem jq_inv_eq : (jq⁻¹ : LaurentSeries ℚ) =
    HahnSeries.single (1 : ℤ) (1 : ℚ) * ((jNumQ⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ) := by
  have hc : PowerSeries.constantCoeff jNumQ ≠ 0 := by rw [constantCoeff_jNumQ]; exact one_ne_zero
  have h0 : HahnSeries.single (1 : ℤ) (1 : ℚ) * jq ≠ 0 := by
    rw [single_mul_jq]; intro h
    have h1 : ((jNumQ : PowerSeries ℚ) : LaurentSeries ℚ).coeff 0 = (0 : LaurentSeries ℚ).coeff 0 := by rw [h]
    rw [coeff_zero_coe_powerSeries, constantCoeff_jNumQ, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1
  have hinv : (HahnSeries.single (1 : ℤ) (1 : ℚ) * jq)⁻¹ = ((jNumQ⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ) := by
    apply mul_left_cancel₀ h0
    rw [mul_inv_cancel₀ h0, single_mul_jq, ← map_mul, PowerSeries.mul_inv_cancel _ hc, map_one]
  have h𝔮0 : (HahnSeries.single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  rw [← hinv, mul_inv, ← mul_assoc, mul_inv_cancel₀ h𝔮0, one_mul]

theorem jq_inv_coeff_zero : (jq⁻¹ : LaurentSeries ℚ).coeff 0 = 0 := by
  rw [jq_inv_eq, HahnSeries.coeff_single_mul, one_mul, show (0 : ℤ) - 1 = -1 by norm_num,
    HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by rintro ⟨m, hm⟩; simp at hm)

omit [Fact p.Prime] in
theorem coe_natCast_coeff_zero :
    ((((p : ↥(chartAlgInf M p)) : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)).coeff 0 = p := by
  rw [SubringClass.coe_natCast, SubringClass.coe_natCast, ← map_natCast (algebraMap ℚ (LaurentSeries ℚ)) p,
    ModularCurve.algebraMap_apply_eq_single, HahnSeries.coeff_single_same]

variable {M p}

theorem natCast_mem (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    (p : ↥(chartAlgInf M p)) ∈ u.asIdeal :=
  (hu _).mpr ⟨1, Subring.one_mem _, by rw [coe_natCast_coeff_zero, mul_one]⟩

theorem jInv_mem (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    jInvChartInf M p ∈ u.asIdeal :=
  (hu _).mpr ⟨0, Subring.zero_mem _, by rw [mul_zero, coe_jInvChartInf, IntermediateField.coe_inv]; exact jq_inv_coeff_zero⟩

theorem jInv_ne_zero : jInvChartInf M p ≠ 0 := by
  intro h
  have h1 : ((jInvChartInf M p : ↥(chartAlgInf M p)) : ↥(modularFunctionFieldFull M)) =
      ((0 : ↥(chartAlgInf M p)) : ↥(modularFunctionFieldFull M)) := by rw [h]
  rw [coe_jInvChartInf, ZeroMemClass.coe_zero] at h1
  exact inv_ne_zero (jFull_ne_zero M) h1

theorem asIdeal_ne_bot (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    u.asIdeal ≠ ⊥ := fun h => jInv_ne_zero (by simpa [h] using jInv_mem u hu)

variable (M p)

theorem phi_C (a : ↥(GaloisRep.ratLocalizedAt p)) :
    phi M p (Polynomial.C a) = algebraMap _ ↥(chartAlgInf M p) a := by
  simp [phi]

theorem phi_X : phi M p Polynomial.X = jInvChartInf M p := by
  simp [phi]

theorem isNoetherianRing_chartAlgInf : IsNoetherianRing ↥(chartAlgInf M p) := by
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  exact @Algebra.FiniteType.isNoetherianRing ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgInf M p) _ _ _
    (finiteType_chartAlgFin_and_chartAlgInf M p).2 inferInstance

variable {M p}

theorem g_apply (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) :
    ((g M p).base u).asIdeal = Ideal.comap (phi M p).toRingHom u.asIdeal := rfl

theorem C_natCast_mem (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    (Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p))) ∈ ((g M p).base u).asIdeal := by
  rw [g_apply, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, phi_C, map_natCast]
  exact natCast_mem u hu

theorem X_mem (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    (Polynomial.X : (↥(GaloisRep.ratLocalizedAt p))[X]) ∈ ((g M p).base u).asIdeal := by
  rw [g_apply, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, phi_X]
  exact jInv_mem u hu

theorem stalkMap_algebraMap (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (r : (↥(GaloisRep.ratLocalizedAt p))[X]) :
    ((g M p).stalkMap u).hom (algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] _ r) =
      algebraMap ↥(chartAlgInf M p) ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) (phi M p r) :=
  AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom (phi M p).toRingHom) u r

theorem stalkMap_comp_algebraMap (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) :
    ((g M p).stalkMap u).hom.comp (algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] _) =
      (algebraMap ↥(chartAlgInf M p) ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u)).comp (phi M p).toRingHom :=
  RingHom.ext fun r => stalkMap_algebraMap u r

theorem stalk_regular (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    IsRegularLocalRing ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) ∧
    ringKrullDim ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) = 2 ∧
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) =
      Ideal.span {algebraMap ↥(chartAlgInf M p) ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) (p : ↥(chartAlgInf M p)),
        algebraMap ↥(chartAlgInf M p) ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) (jInvChartInf M p)} := by
  haveI : u.asIdeal.IsPrime := u.isPrime
  obtain ⟨h1, h2, h3⟩ := ModularCurve.IgusaScheme.isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_cuspInfty
    M p u.asIdeal hu ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u)
  refine ⟨h1, h2, ?_⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal u.asIdeal ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u), h3]

end Aux

attribute [local instance] algStalkB algStalkP isLocalization_stalkB isLocalization_stalkP

theorem flat_stalkMap_g (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    ((g M p).stalkMap u).hom.Flat := by
  classical
  haveI : u.asIdeal.IsPrime := u.isPrime
  haveI hDVR : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

  let R : Type := ↑((Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])).presheaf.stalk ((g M p).base u))
  let S : Type := ↑((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u)
  let f : R →+* S := ((g M p).stalkMap u).hom
  letI algRS : Algebra R S := f.toAlgebra
  change Module.Flat R S
  haveI : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom ((g M p).stalkMap u).hom)
  haveI : IsNoetherianRing ↥(chartAlgInf M p) := isNoetherianRing_chartAlgInf M p
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing u.asIdeal.primeCompl S inferInstance
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing ((g M p).base u).asIdeal.primeCompl R inferInstance
  haveI : IsScalarTower R S S := IsScalarTower.right
  obtain ⟨hreg, hdim, hmax⟩ := stalk_regular u hu
  haveI := hreg
  haveI : IsDomain S := IsRegularLocalRing.isDomain S

  set sp : S := algebraMap ↥(chartAlgInf M p) S (p : ↥(chartAlgInf M p)) with hsp
  set st : S := algebraMap ↥(chartAlgInf M p) S (jInvChartInf M p) with hst
  set rp : R := algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] R (Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p))) with hrp
  set rX : R := algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] R Polynomial.X with hrX
  have hfp : f rp = sp := by
    rw [hrp, hsp]; erw [stalkMap_algebraMap]; rw [phi_C, map_natCast]
  have hfX : f rX = st := by
    rw [hrX, hst]; erw [stalkMap_algebraMap]; rw [phi_X]
  have hinjS : Function.Injective (algebraMap ↥(chartAlgInf M p) S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors u.asIdeal)
  have hsp_ne : sp ≠ 0 := by
    intro h
    have h0 : (p : ↥(chartAlgInf M p)) = 0 := hinjS (by rw [map_zero]; exact h)
    have := coe_natCast_coeff_zero M p
    rw [h0, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this.symm)
  have hst_ne : st ≠ 0 := fun h => jInv_ne_zero (hinjS (by rw [map_zero]; exact h))

  have hPmax : ((g M p).base u).asIdeal =
      Ideal.span {Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)), Polynomial.X} := by

    let ev : (↥(GaloisRep.ratLocalizedAt p))[X] →+* IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p) :=
      (IsLocalRing.residue _).comp (Polynomial.evalRingHom 0)
    have hev : Function.Surjective ev := (IsLocalRing.residue_surjective).comp
      (fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩)
    have hmA := GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out
    have hker : RingHom.ker ev = Ideal.span {Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)), Polynomial.X} := by
      apply le_antisymm
      · intro q hq
        rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmA,
          Ideal.mem_span_singleton', Polynomial.coe_evalRingHom] at hq
        obtain ⟨a, ha⟩ := hq
        obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := q)
        have hq' : q = Polynomial.X * r + Polynomial.C a * Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)) := by
          rw [← hr, ← Polynomial.C_mul, ha, Polynomial.coeff_zero_eq_eval_zero, sub_add_cancel]
        rw [hq']
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · rw [Ideal.span_le]
        rintro x (rfl | rfl)
        · change ev _ = 0
          rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C, IsLocalRing.residue_eq_zero_iff, hmA]
          exact Ideal.mem_span_singleton_self _
        · change ev _ = 0
          rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]
    have hImax : (Ideal.span {Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)), Polynomial.X}).IsMaximal := by
      rw [← hker]; exact RingHom.ker_isMaximal_of_surjective ev hev
    refine (hImax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact C_natCast_mem u hu
    · exact X_mem u hu
  have hmR : IsLocalRing.maximalIdeal R = Ideal.ofList [rp, rX] := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal ((g M p).base u).asIdeal R, hPmax, Ideal.map_span,
      Set.image_insert_eq, Set.image_singleton, Ideal.ofList_cons, Ideal.ofList_singleton, ← Ideal.span_insert]

  have hsp_mem : sp ∈ IsLocalRing.maximalIdeal S := hmax ▸ Ideal.subset_span (by simp)
  have hst_mem : st ∈ IsLocalRing.maximalIdeal S := hmax ▸ Ideal.subset_span (by simp)
  have hrank : (IsLocalRing.maximalIdeal S).spanFinrank = 2 := by
    have h := hreg.spanFinrank_maximalIdeal
    rw [hdim] at h
    exact_mod_cast h
  have hne_span : ∀ x : S, IsLocalRing.maximalIdeal S ≠ Ideal.span {x} := by
    intro x hx
    have h1 : (IsLocalRing.maximalIdeal S).spanFinrank ≤ 1 := by
      rw [hx]
      exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans (by simp)
    omega

  have hsp_nsq : sp ∉ IsLocalRing.maximalIdeal S ^ 2 := by
    intro h2
    apply hne_span st
    apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem _).mpr hst_mem)
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    conv_lhs => rw [hmax]
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · refine Submodule.mem_sup_right ?_
      change sp ∈ IsLocalRing.maximalIdeal S * IsLocalRing.maximalIdeal S
      rw [← pow_two]
      exact h2
    · exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)

  haveI : Nontrivial (S ⧸ Ideal.span {sp}) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h => (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr hsp_mem)))
  haveI : IsLocalRing (S ⧸ Ideal.span {sp}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmin : ∀ q ∈ minimalPrimes S, sp ∉ q := by
    intro q hq
    rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hq
    subst hq
    simpa using hsp_ne
  obtain ⟨hregQ, -⟩ := IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    S hsp_mem hsp_nsq hmin
  haveI := hregQ
  haveI : IsDomain (S ⧸ Ideal.span {sp}) := IsRegularLocalRing.isDomain _
  have hprime : (Ideal.span {sp}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hst_notMem : st ∉ Ideal.span {sp} := by
    intro h
    apply hne_span sp
    apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem _).mpr hsp_mem)
    rw [hmax, Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.mem_span_singleton_self _
    · exact h

  have hwreg : RingTheory.Sequence.IsWeaklyRegular S [rp, rX] := by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨?_, ?_, RingTheory.Sequence.IsWeaklyRegular.nil R _⟩
    · refine IsSMulRegular.of_right_eq_zero_of_smul fun s hs => ?_
      change f rp * s = 0 at hs
      rw [hfp] at hs
      exact (mul_eq_zero.mp hs).resolve_left hsp_ne
    · refine IsSMulRegular.of_right_eq_zero_of_smul fun x hx => ?_
      induction x using Submodule.Quotient.induction_on with
      | H s =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.Quotient.mk_eq_zero]
        obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        change f rp * b = f rX * s at hb
        rw [hfp, hfX] at hb
        have hmem : st * s ∈ Ideal.span {sp} := hb ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self sp)
        rcases hprime.mem_or_mem hmem with h | h
        · exact absurd h hst_notMem
        · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
          exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
            ⟨c, trivial, by change f rp * c = s; rw [hfp, mul_comm]; exact hc⟩

  have htor := RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList hwreg
  apply Module.flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField (R := R) (S := S) (M := S)
  change IsZero (((Tor (ModuleCat.{0} R) 1).obj (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))).obj (ModuleCat.of R S))
  rw [hmR]
  exact htor

theorem map_maximalIdeal_stalkMap_g (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    Ideal.map ((g M p).stalkMap u).hom
        (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])).presheaf.stalk ((g M p).base u))) =
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) := by
  haveI : u.asIdeal.IsPrime := u.isPrime
  obtain ⟨-, -, hmax⟩ := stalk_regular u hu

  have hR : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])).presheaf.stalk ((g M p).base u)) =
      Ideal.map (algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] _) ((g M p).base u).asIdeal :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal ((g M p).base u).asIdeal _).symm
  have hS : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ↥(chartAlgInf M p))).presheaf.stalk u) =
      Ideal.map (algebraMap ↥(chartAlgInf M p) _) u.asIdeal :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal u.asIdeal _).symm
  rw [hR, Ideal.map_map, stalkMap_comp_algebraMap, ← Ideal.map_map]
  apply le_antisymm
  · rw [hS]
    exact Ideal.map_mono Ideal.map_comap_le
  · rw [hmax, Ideal.span_le]
    rintro x (rfl | rfl)
    · refine Ideal.mem_map_of_mem _ ?_
      have h := Ideal.mem_map_of_mem (phi M p).toRingHom (C_natCast_mem u hu)
      rwa [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, phi_C, map_natCast] at h
    · refine Ideal.mem_map_of_mem _ ?_
      have h := Ideal.mem_map_of_mem (phi M p).toRingHom (X_mem u hu)
      rwa [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, phi_X] at h

theorem isIso_residueFieldMap_g (u : Spec (CommRingCat.of ↥(chartAlgInf M p))) (hu : IsCuspPrime M p u) :
    IsIso ((g M p).residueFieldMap u) := by
  classical
  haveI : u.asIdeal.IsPrime := u.isPrime
  let Y := Spec (CommRingCat.of (↥(GaloisRep.ratLocalizedAt p))[X])
  let Xs := Spec (CommRingCat.of ↥(chartAlgInf M p))
  let R : Type := ↑(Y.presheaf.stalk ((g M p).base u))
  let S : Type := ↑(Xs.presheaf.stalk u)
  let ρ : ↑(Y.residueField ((g M p).base u)) →+* ↑(Xs.residueField u) := ((g M p).residueFieldMap u).hom

  have hρ : ∀ r : R, ρ (Y.residue ((g M p).base u) r) = Xs.residue u (((g M p).stalkMap u).hom r) := fun r =>
    CategoryTheory.ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap (g M p) u) r

  obtain ⟨φinf, hφinf⟩ := ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_eq_coeff_zero M p
  have hcoeA : ∀ a : ↥(GaloisRep.ratLocalizedAt p),
      (((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgInf M p) a : ↥(chartAlgInf M p)) :
        ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (a : ℚ) := by
    intro a
    rw [Subalgebra.coe_algebraMap]
    change ((algebraMap ℚ ↥(modularFunctionFieldFull M) (a : ℚ) : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ) = _
    rw [eq_ratCast (algebraMap ℚ ↥(modularFunctionFieldFull M)), SubfieldClass.coe_ratCast,
      ← eq_ratCast (algebraMap ℚ (LaurentSeries ℚ))]
  have hB : ∀ b : ↥(chartAlgInf M p), ∃ y, ρ y = Xs.residue u (algebraMap ↥(chartAlgInf M p) S b) := by
    intro b
    have hbu : b - algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgInf M p) (φinf b) ∈ u.asIdeal := by
      refine (hu _).mpr ⟨0, Subring.zero_mem _, ?_⟩
      rw [mul_zero, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, hcoeA,
        ModularCurve.algebraMap_apply_eq_single, HahnSeries.coeff_single_same, ← hφinf b, sub_self]
    refine ⟨Y.residue ((g M p).base u) (algebraMap (↥(GaloisRep.ratLocalizedAt p))[X] R (Polynomial.C (φinf b))), ?_⟩
    rw [hρ]
    erw [stalkMap_algebraMap]
    rw [phi_C]

    change IsLocalRing.residue S _ = IsLocalRing.residue S _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← map_sub,
      IsLocalization.AtPrime.to_map_mem_maximal_iff S u.asIdeal, ← neg_sub]
    exact u.asIdeal.neg_mem hbu

  have hsurj : Function.Surjective ρ := by
    intro x
    obtain ⟨s, rfl⟩ := Xs.residue_surjective u x
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj u.asIdeal.primeCompl (s : S)
    obtain ⟨yb, hyb⟩ := hB b
    obtain ⟨yc, hyc⟩ := hB c
    have hc0 : Xs.residue u (algebraMap ↥(chartAlgInf M p) S c) ≠ 0 := by
      change IsLocalRing.residue S _ ≠ 0
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff S u.asIdeal]
      exact c.2
    refine ⟨yb * yc⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hyb, hyc]
    rw [mul_inv_eq_iff_eq_mul₀ hc0, ← map_mul]
    change IsLocalRing.residue S _ = IsLocalRing.residue S _
    exact congrArg _ hbc.symm
  have hbij : Function.Bijective ρ := ⟨ρ.injective, hsurj⟩
  have he : (g M p).residueFieldMap u = (RingEquiv.ofBijective ρ hbij).toCommRingCatIso.hom := rfl
  rw [he]
  infer_instance

end Stalk

theorem locallyOfFinitePresentation_g : LocallyOfFinitePresentation (g M p) := by
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p (Fact.out)
  rw [g, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  show (phi M p).toRingHom.FinitePresentation
  rw [← RingHom.FinitePresentation.of_finiteType]
  apply RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap ↥(GaloisRep.ratLocalizedAt p) (↥(GaloisRep.ratLocalizedAt p))[X])
  rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, RingHom.finiteType_algebraMap]
  exact (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf M p).2

theorem isCuspPrime_of_section
    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (igusaTo M p))
    (rhoInf : ↥(IgusaScheme.chartAlgInf M p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf M p),
      ((rhoInf b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0)
    (t : ↥(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (ht : t.asIdeal ≠ ⊥) :
    IsCuspPrime M p ((Spec.map (CommRingCat.ofHom rhoInf.toRingHom)).base t) := by
  intro b
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  have hmax : t.asIdeal = IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal ht)
  have hspan := GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out
  show b ∈ Ideal.comap rhoInf.toRingHom t.asIdeal ↔ _
  rw [Ideal.mem_comap, hmax, hspan, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    have hc' : rhoInf b = c * (p : ↥(GaloisRep.ratLocalizedAt p)) := hc.symm
    refine ⟨(c : ℚ), c.2, ?_⟩
    rw [← hrho b, hc', Subring.coe_mul, Subring.coe_natCast, mul_comm]
  · rintro ⟨c, hc, hbc⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    show (((⟨c, hc⟩ : ↥(GaloisRep.ratLocalizedAt p)) * (p : ↥(GaloisRep.ratLocalizedAt p)) :
        ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((rhoInf b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
    rw [Subring.coe_mul, Subring.coe_natCast, hrho b, hbc, mul_comm]

end IgusaCuspSmooth

open IgusaCuspSmooth in

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (igusaTo M p))
    (rhoInf : ↥(IgusaScheme.chartAlgInf M p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf M p),
      ((rhoInf b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf M p)
    (t : ↥(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (ht : t.asIdeal ≠ ⊥) :
    ∃ W : (ModularCurve.IgusaScheme M p).Opens, εinf.1.base t ∈ W ∧ Smooth (W.ι ≫ igusaTo M p) := by

  set u : Spec (CommRingCat.of ↥(chartAlgInf M p)) := (Spec.map (CommRingCat.ofHom rhoInf.toRingHom)).base t with hu_def
  have hx : εinf.1.base t = (ιInf M p).base u := by rw [hεchart]; rfl
  have hu : IsCuspPrime M p u := isCuspPrime_of_section M p εinf rhoInf hrho t ht
  haveI := locallyOfFinitePresentation_g M p
  haveI := Stalk.isIso_residueFieldMap_g M p u hu

  obtain ⟨V, huV, hV⟩ :=
    AlgebraicGeometry.exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
      (g M p) u (Stalk.flat_stalkMap_g M p u hu) (Stalk.map_maximalIdeal_stalkMap_g M p u hu)
  haveI := hV
  haveI := smooth_affTo p

  have hVsm : Smooth (V.ι ≫ ιInf M p ≫ igusaTo M p) := by
    rw [← g_affTo, ← Category.assoc V.ι]
    infer_instance

  refine ⟨(ιInf M p) ''ᵁ V, ?_, ?_⟩
  · rw [hx]; exact ⟨u, huV, rfl⟩
  · have e : ((ιInf M p) ''ᵁ V).ι ≫ igusaTo M p = ((ιInf M p).isoImage V).inv ≫ (V.ι ≫ ιInf M p ≫ igusaTo M p) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
    rw [e]
    infer_instance

end S_ModularCurve_IgusaScheme_exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot (solution)
