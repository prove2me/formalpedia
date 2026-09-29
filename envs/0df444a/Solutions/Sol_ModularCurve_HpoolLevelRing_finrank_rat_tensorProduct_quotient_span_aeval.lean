-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.finrank_rat_tensorProduct_quotient_span_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/eaf5fe8f-58f3-5d81-a650-cf146e2e8ba8

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_ModularCurve_natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries
import Theorems.Thm_ModularCurve_exists_aeval_jFull_eq_norm_of_mem_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "Polynomial ModularCurve~transcendental_jq P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve.HpoolLevelRing"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "modularUnitSeries jq jqN_one modularFunctionFieldFull IgusaScheme.jFull IgusaScheme natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries exists_aeval_jFull_eq_norm_of_mem_chartAlgFin finiteDimensional_adjoin_jFull_modularFunctionFieldFull jqNModC_rat transcendental_jqNModC"
namespace HpoolLevelRing
p2m_export "ModularCurve.HpoolLevelRing" "Afin levelRing"
namespace OggRankAux
p2m_open "ModularCurve.HpoolLevelRing ModularCurve~transcendental_jq"

open AlgebraicCurve.TwoChartIntegralModel

variable (p : ℕ) [Fact p.Prime] [NeZero p]

abbrev FF : Type := ↥(modularFunctionFieldFull p)

noncomputable abbrev jF : FF p := IgusaScheme.jFull p

abbrev Bq : Type := ↥(chartAlg ℚ (FF p) {jF p})

noncomputable abbrev jA : Afin p := jChartFin ℤ (FF p) (jF p)

noncomputable abbrev jB : Bq p := jChartFin ℚ (FF p) (jF p)

noncomputable abbrev Kj : IntermediateField ℚ (FF p) := IntermediateField.adjoin ℚ ({jF p} : Set (FF p))

noncomputable abbrev jK : ↥(Kj p) := ⟨jF p, IntermediateField.mem_adjoin_simple_self ℚ (jF p)⟩

scoped instance instIsScalarTowerRatLaurent : IsScalarTower ℚ ℚ (LaurentSeries ℚ) := ⟨fun a b c => mul_smul a b c⟩

omit [Fact p.Prime] [NeZero p] in
theorem transcendental_jq : Transcendental ℚ jq := by
  have h := ModularCurve.transcendental_jqNModC ℚ 1
  rwa [jqNModC_rat, jqN_one] at h

omit [Fact p.Prime] in
theorem transcendental_jF : Transcendental ℚ (jF p) := by
  intro halg
  apply transcendental_jq
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  let ι : FF p →+* LaurentSeries ℚ := SubringClass.subtype (modularFunctionFieldFull p)
  have h := congrArg ι hP
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
  have hring : ι.comp (algebraMap ℚ (FF p)) = algebraMap ℚ (LaurentSeries ℚ) := RingHom.ext_rat _ _
  rw [hring] at h
  rw [Polynomial.aeval_def]
  exact h

scoped instance finiteDimensional_Kj : FiniteDimensional ↥(Kj p) (FF p) :=
  ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p

example : Algebra.IsSeparable ↥(Kj p) (FF p) := inferInstance

@[reducible] noncomputable def algQXB : Algebra ℚ[X] (Bq p) := (Polynomial.aeval (jB p)).toRingHom.toAlgebra

@[reducible] noncomputable def algQXF : Algebra ℚ[X] (FF p) := (Polynomial.aeval (jF p)).toRingHom.toAlgebra

@[reducible] noncomputable def algQXK : Algebra ℚ[X] ↥(Kj p) := (Polynomial.aeval (jK p)).toRingHom.toAlgebra

attribute [local instance] algQXB algQXF algQXK

theorem algebraMap_QXB (f : ℚ[X]) : algebraMap ℚ[X] (Bq p) f = aeval (jB p) f := rfl
theorem algebraMap_QXF (f : ℚ[X]) : algebraMap ℚ[X] (FF p) f = aeval (jF p) f := rfl
theorem algebraMap_QXK (f : ℚ[X]) : algebraMap ℚ[X] ↥(Kj p) f = aeval (jK p) f := rfl

scoped instance tower_QXBF : IsScalarTower ℚ[X] (Bq p) (FF p) := by
  refine IsScalarTower.of_algebraMap_eq fun f => ?_
  rw [algebraMap_QXB, algebraMap_QXF]
  change aeval (jF p) f = (chartAlg ℚ (FF p) {jF p}).val (aeval (jB p) f)
  rw [← aeval_algHom_apply]
  rfl

scoped instance tower_QXKF : IsScalarTower ℚ[X] ↥(Kj p) (FF p) := by
  refine IsScalarTower.of_algebraMap_eq fun f => ?_
  rw [algebraMap_QXK, algebraMap_QXF]
  change aeval (jF p) f = (Kj p).val (aeval (jK p) f)
  rw [← aeval_algHom_apply]
  rfl

scoped instance tower_QQXB : IsScalarTower ℚ ℚ[X] (Bq p) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    rw [algebraMap_QXB, Polynomial.algebraMap_apply, aeval_C]
    rfl

scoped instance tower_QQXK : IsScalarTower ℚ ℚ[X] ↥(Kj p) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    rw [algebraMap_QXK, Polynomial.algebraMap_apply, aeval_C]
    rfl

scoped instance tower_QQXF : IsScalarTower ℚ ℚ[X] (FF p) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    rw [algebraMap_QXF, Polynomial.algebraMap_apply, aeval_C]
    rfl

theorem algebraMap_QXF_injective : Function.Injective (algebraMap ℚ[X] (FF p)) :=
  transcendental_iff_injective.mp (transcendental_jF p)

theorem algebraMap_QXB_injective : Function.Injective (algebraMap ℚ[X] (Bq p)) := fun f g h => by
  apply algebraMap_QXF_injective p
  rw [IsScalarTower.algebraMap_apply ℚ[X] (Bq p) (FF p), h, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_QXK_injective : Function.Injective (algebraMap ℚ[X] ↥(Kj p)) := fun f g h => by
  apply algebraMap_QXF_injective p
  rw [IsScalarTower.algebraMap_apply ℚ[X] ↥(Kj p) (FF p), h, ← IsScalarTower.algebraMap_apply]

scoped instance : Module.IsTorsionFree ℚ[X] (FF p) where
  isSMulRegular r hr := by
    intro x y hxy
    have hr0 : algebraMap ℚ[X] (FF p) r ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_QXF_injective p)).mpr hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
scoped instance : Module.IsTorsionFree ℚ[X] (Bq p) where
  isSMulRegular r hr := by
    intro x y hxy
    have hr0 : algebraMap ℚ[X] (Bq p) r ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_QXB_injective p)).mpr hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
scoped instance : FaithfulSMul ℚ[X] (Bq p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_QXB_injective p)

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in

scoped instance isFractionRing_QXK : IsFractionRing ℚ[X] ↥(Kj p) := by
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental ℚ (FF p) (jF p)
    (transcendental_jF p)
  have halg : ∀ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f = aeval RatFunc.X f := fun f => by
    have h1 := aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X f
    rw [aeval_X_left, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_X] at h1
    exact h1.symm
  have hcomm : ∀ f : ℚ[X], e.symm.toRingEquiv (algebraMap ℚ[X] (RatFunc ℚ) f) = algebraMap ℚ[X] ↥(Kj p) f := by
    intro f
    rw [algebraMap_QXK, halg, AlgEquiv.coe_ringEquiv, ← aeval_algHom_apply,
      ← he, AlgEquiv.symm_apply_apply]
  let e' : RatFunc ℚ ≃ₐ[ℚ[X]] ↥(Kj p) := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) hcomm
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors ℚ[X]) e'

noncomputable abbrev A0 : Subalgebra ℚ (FF p) := Algebra.adjoin ℚ ({jF p} : Set (FF p))

theorem aeval_mem_A0 (f : ℚ[X]) : aeval (jF p) f ∈ A0 p := by
  rw [A0, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨f, rfl⟩

@[reducible] noncomputable def algQXA0 : Algebra ℚ[X] ↥(A0 p) :=
  ((Polynomial.aeval (jF p)).codRestrict (A0 p) (aeval_mem_A0 p)).toRingHom.toAlgebra

attribute [local instance] algQXA0

scoped instance tower_QXA0F : IsScalarTower ℚ[X] ↥(A0 p) (FF p) :=
  IsScalarTower.of_algebraMap_eq fun f => rfl

theorem algebraMap_QXA0_surjective : Function.Surjective (algebraMap ℚ[X] ↥(A0 p)) := by
  rintro ⟨a, ha⟩
  rw [A0, Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  exact ⟨f, rfl⟩

scoped instance : Algebra.IsIntegral ℚ[X] ↥(A0 p) :=
  ⟨fun a => by
    obtain ⟨f, rfl⟩ := algebraMap_QXA0_surjective p a
    exact isIntegral_algebraMap⟩

scoped instance isIntegralClosure_B : IsIntegralClosure (Bq p) ℚ[X] (FF p) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := fun {x} => by
    constructor
    · intro hx
      refine ⟨⟨x, (mem_chartAlg_iff ℚ (FF p)).mpr ?_⟩, rfl⟩
      exact hx.tower_top
    · rintro ⟨y, rfl⟩
      have hy : IsIntegral ↥(A0 p) (y : FF p) := (mem_chartAlg_iff ℚ (FF p)).mp y.2
      exact isIntegral_trans (y : FF p) hy

scoped instance : Module.Finite ℚ[X] (Bq p) := IsIntegralClosure.finite ℚ[X] ↥(Kj p) (FF p) (Bq p)
scoped instance : Module.Free ℚ[X] (Bq p) := inferInstance
scoped instance : IsDedekindDomain (Bq p) := IsIntegralClosure.isDedekindDomain ℚ[X] ↥(Kj p) (FF p) (Bq p)

set_option maxHeartbeats 3200000 in
theorem natDegree_norm (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (x : Bq p) (hxA : (x : FF p) ∈ chartAlgFin ℤ (FF p) (jF p))
    (v : FF p)
    (hv : v = ⟨modularUnitSeries p, hmem⟩ ∨ v = (p : FF p) ^ 12 * (⟨modularUnitSeries p, hmem⟩)⁻¹)
    (g : ℤ[X]) (hg : g.Monic) (hD : 1 ≤ g.natDegree) (h0 : g.coeff 0 ≠ 0)
    (hx : (x : FF p) = Polynomial.aeval v g) :
    (Algebra.norm ℚ[X] x).natDegree = g.natDegree * (p - 1) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (Bq p) (nonZeroDivisors ℚ[X])) (FF p) :=
    IsIntegralClosure.isLocalization ℚ[X] ↥(Kj p) (FF p) (Bq p)
  obtain ⟨N, hN⟩ := ModularCurve.exists_aeval_jFull_eq_norm_of_mem_chartAlgFin p (x : FF p) hxA
  have hdeg := ModularCurve.natDegree_eq_mul_of_aeval_jFull_eq_norm_aeval_modularUnitSeries p hmem v hv g hg
    hD h0 N (by rw [hN, ← hx])
  have hloc : Algebra.norm ↥(Kj p) (algebraMap (Bq p) (FF p) x) = algebraMap ℚ[X] ↥(Kj p) (Algebra.norm ℚ[X] x) :=
    Algebra.norm_localization ℚ[X] (nonZeroDivisors ℚ[X]) x
  have hmapN : N.map (algebraMap ℤ ℚ) = Algebra.norm ℚ[X] x := by
    apply algebraMap_QXF_injective p
    rw [algebraMap_QXF, algebraMap_QXF, Polynomial.aeval_map_algebraMap,
      ← algebraMap_QXF, IsScalarTower.algebraMap_apply ℚ[X] ↥(Kj p) (FF p), ← hloc]
    exact hN
  rw [← hmapN, Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int, hdeg]

set_option maxHeartbeats 3200000 in
private theorem _root_.ModularCurve.HpoolLevelRing.OggRankAux.finrank_eq (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) (v : Afin p)
    (hv : (v : FF p) = ⟨modularUnitSeries p, hmem⟩ ∨ (v : FF p) = (p : FF p) ^ 12 * (⟨modularUnitSeries p, hmem⟩)⁻¹)
    (g : ℤ[X]) (hg : g.Monic) (hg0 : g.eval 0 ≠ 0) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Afin p ⧸ Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval v g}) = (p - 1) * g.natDegree := by
  classical
  obtain ⟨e, he⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg ℤ ℚ (FF p)
    (nonZeroDivisors ℤ) ({jF p} : Set (FF p))
  set x : Afin p := Polynomial.aeval v g with hxdef
  set xq : Bq p := e ((1 : ℚ) ⊗ₜ[ℤ] x) with hxq
  have hxqF : (xq : FF p) = (x : FF p) := by rw [hxq, he, one_smul]
  have hxF : (x : FF p) = Polynomial.aeval (v : FF p) g :=
    (Polynomial.aeval_algHom_apply (chartAlgFin ℤ (FF p) (jF p)).val v g).symm
  have hI : Ideal.span {xq} = (Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] x}).map (e : ℚ ⊗[ℤ] Afin p →+* Bq p) := by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe]
  rw [(Ideal.quotientEquivAlg _ _ e hI).toLinearEquiv.finrank_eq]
  by_cases hD : g.natDegree = 0
  · have hg1 : g = 1 := hg.natDegree_eq_zero.mp hD
    have hx1 : x = 1 := by rw [hxdef, hg1, map_one]
    have hxq1 : xq = 1 := by rw [hxq, hx1]; exact map_one e
    haveI : Subsingleton (Bq p ⧸ Ideal.span {xq}) := by
      rw [Ideal.Quotient.subsingleton_iff, hxq1, Ideal.span_singleton_one]
    rw [hD, mul_zero]
    exact Module.finrank_zero_of_subsingleton
  · have hD1 : 1 ≤ g.natDegree := Nat.one_le_iff_ne_zero.mpr hD
    have h0 : g.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
    have hdeg := natDegree_norm p hmem xq (by rw [hxqF]; exact x.2) (v : FF p) hv g hg hD1 h0 (by rw [hxqF, hxF])
    have hp1 : 1 ≤ p - 1 := Nat.le_sub_one_of_lt (Fact.out : p.Prime).one_lt
    have hxq0 : xq ≠ 0 := by
      intro h
      rw [h, Algebra.norm_zero, Polynomial.natDegree_zero] at hdeg
      exact absurd hdeg.symm (Nat.ne_of_gt (Nat.mul_pos hD1 hp1))
    rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis ℚ[X] (Bq p)) hxq0, hdeg, mul_comm]

p2m_export "ModularCurve.HpoolLevelRing.OggRankAux" "finrank_eq"
end ModularCurve.HpoolLevelRing.OggRankAux
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve.HpoolLevelRing.OggRankAux"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve.HpoolLevelRing"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval.ModularCurve"

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : Afin p)
    (hv : (v : ↥(modularFunctionFieldFull p)) = (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p)) ∨
      (v : ↥(modularFunctionFieldFull p)) = (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹)
    (g : ℤ[X]) (hg : g.Monic) (hg0 : g.eval 0 ≠ 0) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Afin p ⧸ Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval v g}) = (p - 1) * g.natDegree :=
  ModularCurve.HpoolLevelRing.OggRankAux.finrank_eq p hmem v hv g hg hg0

end S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_finrank_rat_tensorProduct_quotient_span_aeval (solution)
