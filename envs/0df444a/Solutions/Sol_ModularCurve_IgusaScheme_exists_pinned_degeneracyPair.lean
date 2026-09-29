-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_pinned_degeneracyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a0430a47-e3bd-5584-9b72-b0c786e2358c

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Theorems.Thm_ModularCurve_forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq
import Theorems.Thm_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_igusaTo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve.IgusaScheme AlgebraicCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin IgusaScheme.igusaTo qExpand qExpand_injective qExpandₐ jq modularFunctionFieldFull jqd_mem_full full_degeneracy_le full_degeneracy_map_le IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf finiteDimensional_adjoin_jFull_modularFunctionFieldFull IgusaScheme.chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast transcendental_jq IgusaScheme.isProper_igusaTo"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull chartAlg mem_chartAlg_iff chartAlgFin chartAlgInf ιFin igusaTo qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg finiteType_chartAlgFin_and_chartAlgInf chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast isProper_igusaTo"
namespace ExistPinned
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (q : ℕ) [Fact q.Prime]

set_option quotPrecheck false in
local notation "ℤq" => ↥(GaloisRep.ratLocalizedAt q)
set_option quotPrecheck false in
local notation "𝔽" N => ↥(modularFunctionFieldFull N)

omit [Fact q.Prime] in
private theorem isFractionRing_base : IsFractionRing ℤq ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
omit [Fact q.Prime] in
private theorem isPIR_base : IsPrincipalIdealRing ℤq := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q

private theorem algebraMap_base_injective (N : ℕ) [NeZero N] : Function.Injective (algebraMap ℤq (𝔽 N)) := by
  haveI := isFractionRing_base q
  rw [IsScalarTower.algebraMap_eq ℤq ℚ (𝔽 N)]
  exact (algebraMap ℚ (𝔽 N)).injective.comp (IsFractionRing.injective ℤq ℚ)

private theorem transcendental_of_coe (N : ℕ) [NeZero N] (x : 𝔽 N)
    (hx : Transcendental ℚ ((x : 𝔽 N) : LaurentSeries ℚ)) : Transcendental ℤq x := by
  haveI := isFractionRing_base q
  have hxℚ : Transcendental ℚ x := by
    intro halg
    obtain ⟨p, hp, hev⟩ := halg
    refine hx ⟨p, hp, ?_⟩
    have h0 : (algebraMap (𝔽 N) (LaurentSeries ℚ)) ((Polynomial.aeval x) p) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  exact fun h => hxℚ ((IsFractionRing.isAlgebraic_iff ℤq ℚ (𝔽 N)).mp h)

private theorem transcendental_jFull (N : ℕ) [NeZero N] : Transcendental ℤq (jFull N) :=
  transcendental_of_coe q N _ (by rw [coe_jFull]; exact transcendental_jq)

private def jℓ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ ∣ N) : 𝔽 N := ⟨qExpand ℚ ℓ jq, jqd_mem_full N hℓ⟩

@[scoped simp] private theorem coe_jℓ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ ∣ N) :
    ((jℓ N ℓ hℓ : 𝔽 N) : LaurentSeries ℚ) = qExpand ℚ ℓ jq := rfl

private theorem transcendental_jℓ (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ ∣ N) : Transcendental ℤq (jℓ N ℓ hℓ) := by
  refine transcendental_of_coe q N _ ?_
  rw [coe_jℓ]
  intro halg
  obtain ⟨p, hp, hev⟩ := halg
  refine transcendental_jq ⟨p, hp, ?_⟩
  have h1 : (Polynomial.aeval (qExpandₐ ℓ jq)) p = qExpandₐ ℓ ((Polynomial.aeval jq) p) :=
    Polynomial.aeval_algHom_apply (qExpandₐ ℓ) jq p
  rw [show qExpand ℚ ℓ jq = qExpandₐ ℓ jq from rfl, h1, ← map_zero (qExpandₐ ℓ)] at hev
  exact qExpand_injective (R := ℚ) ℓ hev

private theorem jℓ_facts (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    jℓ N ℓ hℓ ≠ 0 ∧ jℓ N ℓ hℓ ∈ TwoChartIntegralModel.chartAlgFin ℤq (𝔽 N) (jFull N) ∧
      jFull N ∈ TwoChartIntegralModel.chartAlgFin ℤq (𝔽 N) (jℓ N ℓ hℓ) :=
  ModularCurve.IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg N q ℓ hℓ

omit [Fact q.Prime] in

private theorem adjoin_base_le_adjoin_rat (N : ℕ) [NeZero N] (s : 𝔽 N)
    (a : 𝔽 N) (ha : a ∈ Algebra.adjoin ℤq ({s} : Set (𝔽 N))) :
    a ∈ IntermediateField.adjoin ℚ ({s} : Set (𝔽 N)) :=
  Algebra.adjoin_induction
    (fun _ hy => Set.mem_singleton_iff.mp hy ▸ IntermediateField.mem_adjoin_simple_self ℚ s)
    (fun r => (IntermediateField.adjoin ℚ ({s} : Set (𝔽 N))).algebraMap_mem (algebraMap ℤq ℚ r))
    (fun _ _ _ _ ha hb => add_mem ha hb)
    (fun _ _ _ _ ha hb => mul_mem ha hb)
    ha

include q in

private theorem finiteDimensional_adjoin_jℓ (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jℓ N ℓ hℓ} : Set (𝔽 N))) (𝔽 N) := by
  let s : 𝔽 N := jℓ N ℓ hℓ
  let K1 := IntermediateField.adjoin ℚ ({s} : Set (𝔽 N))
  let A := Algebra.adjoin ℤq ({s} : Set (𝔽 N))

  have hjA : IsIntegral A (jFull N) :=
    (TwoChartIntegralModel.mem_chartAlg_iff ℤq (𝔽 N)).mp (jℓ_facts q N ℓ hℓ).2.2
  let ιAK : A →+* K1 := (Subalgebra.val A).toRingHom.codRestrict K1.toSubring
    (fun a => adjoin_base_le_adjoin_rat q N s a a.2)
  letI : Algebra A K1 := ιAK.toAlgebra
  haveI : IsScalarTower A K1 (𝔽 N) := IsScalarTower.of_algebraMap_eq fun a => rfl
  have hjK1 : IsIntegral K1 (jFull N) := hjA.tower_top

  let K2 := IntermediateField.adjoin K1 ({jFull N} : Set (𝔽 N))
  haveI hK12 : FiniteDimensional K1 K2 := IntermediateField.adjoin.finiteDimensional hjK1

  let E := IntermediateField.adjoin ℚ ({jFull N} : Set (𝔽 N))
  haveI hEF : FiniteDimensional E (𝔽 N) := finiteDimensional_adjoin_jFull_modularFunctionFieldFull N
  have hle : E ≤ K2.restrictScalars ℚ := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx; obtain rfl := hx
    exact IntermediateField.mem_adjoin_simple_self K1 (jFull N)
  letI : Algebra E K2 := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower E K2 (𝔽 N) := IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI hK2F : Module.Finite K2 (𝔽 N) := Module.Finite.of_restrictScalars_finite E K2 (𝔽 N)
  exact Module.Finite.trans K2 (𝔽 N)

private theorem finiteType_charts_jℓ (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    haveI : Fact (jℓ N ℓ hℓ ≠ 0) := ⟨(jℓ_facts q N ℓ hℓ).1⟩
    Algebra.FiniteType ℤq ↥(TwoChartIntegralModel.chartAlgFin ℤq (𝔽 N) (jℓ N ℓ hℓ)) ∧
      Algebra.FiniteType ℤq ↥(TwoChartIntegralModel.chartAlgInf ℤq (𝔽 N) (jℓ N ℓ hℓ)) := by
  haveI : Fact (jℓ N ℓ hℓ ≠ 0) := ⟨(jℓ_facts q N ℓ hℓ).1⟩
  haveI := isFractionRing_base q
  haveI := isPIR_base q
  haveI hFD := finiteDimensional_adjoin_jℓ q N ℓ hℓ
  exact TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf ℤq ℚ (𝔽 N) (jℓ N ℓ hℓ)
    (transcendental_jℓ q N ℓ hℓ) hFD inferInstance

private theorem charts_jFull (N : ℕ) [NeZero N] :
    (IsNoetherianRing ↥(TwoChartIntegralModel.chartAlgFin ℤq (𝔽 N) (jFull N)) ∧
        IsFractionRing ↥(TwoChartIntegralModel.chartAlgFin ℤq (𝔽 N) (jFull N)) (𝔽 N)) ∧
      (IsNoetherianRing ↥(TwoChartIntegralModel.chartAlgInf ℤq (𝔽 N) (jFull N)) ∧
        IsFractionRing ↥(TwoChartIntegralModel.chartAlgInf ℤq (𝔽 N) (jFull N)) (𝔽 N)) := by
  haveI := isFractionRing_base q
  haveI := isPIR_base q
  obtain ⟨hF, hI⟩ := ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N q
  haveI : Algebra.FiniteType ℤq ↥(TwoChartIntegralModel.chartAlgFin ℤq (𝔽 N) (jFull N)) := hF
  haveI : Algebra.FiniteType ℤq ↥(TwoChartIntegralModel.chartAlgInf ℤq (𝔽 N) (jFull N)) := hI
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jFull N} : Set (𝔽 N))) (𝔽 N) :=
    finiteDimensional_adjoin_jFull_modularFunctionFieldFull N
  have hKinv : IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set (𝔽 N)) =
      IntermediateField.adjoin ℚ ({jFull N} : Set (𝔽 N)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.singleton_subset_iff.mpr
        ((IntermediateField.adjoin ℚ _).inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (jFull N)))
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx; obtain rfl := hx
      have h1 := (IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set (𝔽 N))).inv_mem
        (IntermediateField.mem_adjoin_simple_self ℚ (jFull N)⁻¹)
      rwa [inv_inv] at h1
  haveI hFD' : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set (𝔽 N))) (𝔽 N) := by
    rw [hKinv]; exact hFD
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact Algebra.FiniteType.isNoetherianRing ℤq _
  · exact TwoChartIntegralModel.isFractionRing_chartAlg ℤq ℚ (𝔽 N) {jFull N}
  · exact Algebra.FiniteType.isNoetherianRing ℤq _
  · exact TwoChartIntegralModel.isFractionRing_chartAlg ℤq ℚ (𝔽 N) {(jFull N)⁻¹}

private theorem inv_intCast_mem (c : ℤ) (hc : ¬ (q : ℤ) ∣ c) : (c : ℚ)⁻¹ ∈ GaloisRep.ratLocalizedAt q := by
  have hc0 : c ≠ 0 := fun h0 => hc (h0 ▸ dvd_zero _)
  show ((c : ℚ)⁻¹).den.Coprime q
  rw [Rat.inv_intCast_den, if_neg hc0]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun h => hc (Int.natCast_dvd.mpr h))

private theorem vis_transport (N : ℕ) [NeZero N] (j j' : 𝔽 N)
    (h : ∀ y ∈ TwoChartIntegralModel.chartAlg ℤ (𝔽 N) {j'⁻¹}, ∃ s ∈ TwoChartIntegralModel.chartAlg ℤ (𝔽 N) {j⁻¹},
        (∃ a ∈ TwoChartIntegralModel.chartAlg ℤ (𝔽 N) {j⁻¹}, s = 1 + j⁻¹ * a) ∧
          s * y ∈ TwoChartIntegralModel.chartAlg ℤ (𝔽 N) {j⁻¹}) :
    ∀ y ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {j'⁻¹}, ∃ s ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {j⁻¹},
        (∃ a ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {j⁻¹}, s = 1 + j⁻¹ * a) ∧
          s * y ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {j⁻¹} := by
  intro y hy
  have hle : ∀ (S : Set (𝔽 N)) (x : 𝔽 N), x ∈ TwoChartIntegralModel.chartAlg ℤ (𝔽 N) S →
      x ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) S := fun S x hx =>
    TwoChartIntegralModel.chartAlg_le_chartAlg ℤ (𝔽 N) ℤq S hx
  obtain ⟨-, hmem, -⟩ :=
    ModularCurve.IgusaScheme.chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast N q ({j'⁻¹} : Set (𝔽 N))
  obtain ⟨a, c, ha, hc, hca⟩ := (hmem y).mp hy
  obtain ⟨s, hs, ⟨b, hb, hsb⟩, hsa⟩ := h a ha
  refine ⟨s, hle _ _ hs, ⟨b, hle _ _ hb, hsb⟩, ?_⟩

  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (fun h0 => hc (h0 ▸ dvd_zero _) : c ≠ 0)
  let ci : ℤq := ⟨(c : ℚ)⁻¹, inv_intCast_mem q c hc⟩
  have hprod : algebraMap ℤq (𝔽 N) ci * (c : 𝔽 N) = 1 := by
    rw [IsScalarTower.algebraMap_apply ℤq ℚ (𝔽 N)]
    have : (algebraMap ℤq ℚ) ci = (c : ℚ)⁻¹ := rfl
    rw [this, ← map_intCast (algebraMap ℚ (𝔽 N)) c, ← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hsy : s * y = algebraMap ℤq (𝔽 N) ci * (s * a) := by
    rw [← hca, ← mul_assoc, ← mul_assoc, mul_comm (algebraMap ℤq (𝔽 N) ci) s, mul_assoc s, hprod, mul_one]
  rw [hsy]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ ci) (hle _ _ hsa)

private theorem vis_jℓ (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    (∀ y ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jℓ N ℓ hℓ)⁻¹},
        ∃ s ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jFull N)⁻¹},
          (∃ a ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jFull N)⁻¹}, s = 1 + (jFull N)⁻¹ * a) ∧
            s * y ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jFull N)⁻¹}) ∧
    (∀ y ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jFull N)⁻¹},
        ∃ s ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jℓ N ℓ hℓ)⁻¹},
          (∃ a ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jℓ N ℓ hℓ)⁻¹}, s = 1 + (jℓ N ℓ hℓ)⁻¹ * a) ∧
            s * y ∈ TwoChartIntegralModel.chartAlg ℤq (𝔽 N) {(jℓ N ℓ hℓ)⁻¹}) := by
  haveI : Fact (jℓ N ℓ hℓ ≠ 0) := ⟨(jℓ_facts q N ℓ hℓ).1⟩
  obtain ⟨hv, hv'⟩ := ModularCurve.forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand N ℓ
    (jℓ N ℓ hℓ) (coe_jℓ N ℓ hℓ)
  exact ⟨vis_transport q N (jFull N) (jℓ N ℓ hℓ) hv, vis_transport q N (jℓ N ℓ hℓ) (jFull N) hv'⟩

section Emb
variable (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime] [NeZero (M * ℓ)]

private theorem le_full : modularFunctionFieldFull M ≤ modularFunctionFieldFull (M * ℓ) :=
  full_degeneracy_le (dvd_mul_right M ℓ)

private theorem coe_algebraMap_base (N : ℕ) [NeZero N] (r : ℤq) :
    ((algebraMap ℤq (𝔽 N) r : 𝔽 N) : LaurentSeries ℚ) = ((algebraMap ℤq ℚ r : ℚ) : LaurentSeries ℚ) := by
  rw [IsScalarTower.algebraMap_apply ℤq ℚ (𝔽 N)]
  simp

private def φ₁ : (𝔽 M) →ₐ[ℤq] (𝔽 (M * ℓ)) where
  toFun x := ⟨(x : LaurentSeries ℚ), le_full M ℓ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp only [coe_algebraMap_base])

private theorem coe_φ₁ (x : 𝔽 M) : ((φ₁ q M ℓ x : 𝔽 (M * ℓ)) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) :=
  @Subtype.coe_mk (LaurentSeries ℚ) (· ∈ modularFunctionFieldFull (M * ℓ)) (x : LaurentSeries ℚ) (le_full M ℓ x.2)

private def φ₂ℚ : (𝔽 M) →ₐ[ℚ] (𝔽 (M * ℓ)) where
  toFun x := ⟨qExpand ℚ ℓ (x : LaurentSeries ℚ),
    full_degeneracy_map_le M ℓ ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by
    show qExpand ℚ ℓ ((algebraMap ℚ (𝔽 M) r : 𝔽 M) : LaurentSeries ℚ) = ((algebraMap ℚ (𝔽 (M * ℓ)) r : 𝔽 (M*ℓ)) : LaurentSeries ℚ)
    rw [show qExpand ℚ ℓ = (qExpandₐ ℓ : LaurentSeries ℚ → LaurentSeries ℚ) from rfl]
    simp)

private def φ₂ : (𝔽 M) →ₐ[ℤq] (𝔽 (M * ℓ)) := (φ₂ℚ M ℓ).restrictScalars ℤq

private theorem coe_φ₂ (x : 𝔽 M) :
    ((φ₂ q M ℓ x : 𝔽 (M * ℓ)) : LaurentSeries ℚ) = qExpand ℚ ℓ (x : LaurentSeries ℚ) := rfl

private theorem φ₁_jFull : φ₁ q M ℓ (jFull M) = jFull (M * ℓ) :=
  Subtype.ext ((coe_φ₁ q M ℓ _).trans ((coe_jFull M).trans (coe_jFull (M * ℓ)).symm))

private theorem φ₂_jFull : φ₂ q M ℓ (jFull M) = jℓ (M * ℓ) ℓ (dvd_mul_left ℓ M) :=
  Subtype.ext ((coe_φ₂ q M ℓ _).trans (by rw [coe_jFull, coe_jℓ]))

private theorem d_pos : 0 < (if ℓ ∣ M then ℓ else ℓ + 1) := by
  have := (Fact.out : ℓ.Prime).pos
  split_ifs <;> omega

private theorem φ₁_finite : (φ₁ q M ℓ).toRingHom.Finite := by
  have h := ModularCurve.finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq M ℓ (M * ℓ) rfl (φ₁ q M ℓ).toRingHom
    (fun f => coe_φ₁ q M ℓ f)
  letI : Algebra (𝔽 M) (𝔽 (M * ℓ)) := (φ₁ q M ℓ).toRingHom.toAlgebra
  have hpos : 0 < Module.finrank (𝔽 M) (𝔽 (M * ℓ)) := by rw [h]; exact d_pos M ℓ
  exact Module.finite_of_finrank_pos hpos

private theorem φ₂_finite : (φ₂ q M ℓ).toRingHom.Finite := by
  have h := ModularCurve.finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand M ℓ (M * ℓ) rfl (φ₂ q M ℓ).toRingHom
    (fun f => coe_φ₂ q M ℓ f)
  letI : Algebra (𝔽 M) (𝔽 (M * ℓ)) := (φ₂ q M ℓ).toRingHom.toAlgebra
  have hpos : 0 < Module.finrank (𝔽 M) (𝔽 (M * ℓ)) := by rw [h]; exact d_pos M ℓ
  exact Module.finite_of_finrank_pos hpos

end Emb

end ModularCurve.IgusaScheme.ExistPinned
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve.IgusaScheme.ExistPinned"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.ModularCurve"

open ModularCurve.IgusaScheme.ExistPinned AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (M q ℓ : ℕ) [NeZero M] [Fact q.Prime] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ) :
    ∃ (π₁ π₂ : SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q))
      (_ : IsFinite π₁.1) (_ : IsFinite π₂.1) (_ : LocallyOfFinitePresentation π₁.1) (_ : LocallyOfFinitePresentation π₂.1)
      (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q)),
      Function.Surjective π₁.1.base ∧ Function.Surjective π₂.1.base ∧
      (∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      (∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιFin M' q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin M q ∧
      IgusaScheme.ιFin M' q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin M q := by
  subst hM'

  haveI hFR : IsFractionRing ↥(GaloisRep.ratLocalizedAt q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  haveI hPIR : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  have hℓM' : ℓ ∣ M * ℓ := dvd_mul_left ℓ M
  haveI hjl0 : Fact (jℓ (M * ℓ) ℓ hℓM' ≠ 0) := ⟨(jℓ_facts q (M * ℓ) ℓ hℓM').1⟩

  obtain ⟨hFfin, hFinf⟩ := charts_jFull q M

  obtain ⟨m₁, ιF₁, ιI₁, hιF₁, -, hm₁b, hm₁F, -, -, -, hm₁fin, hm₁surj⟩ :=
    exists_hom_isFinite_surjective_of_algHom ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M)
      ↥(modularFunctionFieldFull (M * ℓ)) (φ₁ q M ℓ) (φ₁_finite q M ℓ) (jFull M) (jFull (M * ℓ)) (φ₁_jFull q M ℓ) hFfin hFinf

  obtain ⟨m₂, ιF₂, ιI₂, hιF₂, -, hm₂b, hm₂F, -, -, -, hm₂fin, hm₂surj⟩ :=
    exists_hom_isFinite_surjective_of_algHom ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M)
      ↥(modularFunctionFieldFull (M * ℓ)) (φ₂ q M ℓ) (φ₂_finite q M ℓ) (jFull M) (jℓ (M * ℓ) ℓ hℓM') (φ₂_jFull q M ℓ) hFfin hFinf

  obtain ⟨hF', hI'⟩ := ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (M * ℓ) q
  haveI : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt q)
      ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ)) (jFull (M * ℓ))) := hF'
  haveI : Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt q)
      ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ)) (jFull (M * ℓ))) := hI'
  obtain ⟨hFl, hIl⟩ := finiteType_charts_jℓ q (M * ℓ) ℓ hℓM'
  haveI := hFl
  haveI := hIl
  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ))
      (jFull (M * ℓ))) := TwoChartIntegralModel.isIntegral _ _ _
  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ))
      (jℓ (M * ℓ) ℓ hℓM')) := TwoChartIntegralModel.isIntegral _ _ _
  haveI : IsProper (toBase ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ)) (jFull (M * ℓ))) :=
    TwoChartIntegralModel.isProper_toBase _ _ _
  haveI : IsProper (toBase ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ)) (jℓ (M * ℓ) ℓ hℓM')) :=
    TwoChartIntegralModel.isProper_toBase _ _ _
  obtain ⟨hvis, hvis'⟩ := vis_jℓ q (M * ℓ) ℓ hℓM'
  obtain ⟨w, ιFw, -, -, hιFw, -, -, -, hwb, hwF, -⟩ :=
    exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (M * ℓ))
      (jFull (M * ℓ)) (jℓ (M * ℓ) ℓ hℓM') (jℓ_facts q (M * ℓ) ℓ hℓM').2.1 (jℓ_facts q (M * ℓ) ℓ hℓM').2.2 hvis hvis'

  obtain ⟨hF0, hI0⟩ := ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf M q
  haveI := hF0
  haveI := hI0
  haveI : IsProper (IgusaScheme.igusaTo M q) := ModularCurve.IgusaScheme.isProper_igusaTo M q
  haveI : IsLocallyNoetherian (ModularCurve.IgusaScheme M q) :=
    LocallyOfFiniteType.isLocallyNoetherian (IgusaScheme.igusaTo M q)

  let π₁ : SchemeHomOver (IgusaScheme.igusaTo (M * ℓ) q) (IgusaScheme.igusaTo M q) := ⟨m₁, hm₁b⟩
  let π₂ : SchemeHomOver (IgusaScheme.igusaTo (M * ℓ) q) (IgusaScheme.igusaTo M q) :=
    ⟨w.hom ≫ m₂, by rw [Category.assoc]; exact (congrArg (w.hom ≫ ·) hm₂b).trans hwb⟩
  haveI hπ₁fin : IsFinite π₁.1 := hm₁fin
  haveI : IsFinite m₂ := hm₂fin
  haveI hπ₂fin : IsFinite π₂.1 := inferInstanceAs (IsFinite (w.hom ≫ m₂))
  have hπ₁lfp : LocallyOfFinitePresentation π₁.1 := inferInstance
  have hπ₂lfp : LocallyOfFinitePresentation π₂.1 := inferInstance

  have hπ₂surj : Function.Surjective π₂.1.base := by
    intro z
    obtain ⟨y, hy⟩ := hm₂surj z
    obtain ⟨x, hx⟩ := (Scheme.homeoOfIso w).surjective y
    refine ⟨x, ?_⟩
    change m₂.base (w.hom.base x) = z
    rw [← hy, ← hx]
    rfl

  have hpin₁ : IgusaScheme.ιFin (M * ℓ) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ιF₁.toRingHom) ≫ IgusaScheme.ιFin M q :=
    hm₁F.symm
  have hpin₂ : IgusaScheme.ιFin (M * ℓ) q ≫ π₂.1 =
      Spec.map (CommRingCat.ofHom (ιFw.comp ιF₂).toRingHom) ≫ IgusaScheme.ιFin M q := by
    change ιFin _ _ (jFull (M * ℓ)) ≫ w.hom ≫ m₂ = _
    rw [← Category.assoc, hwF, Category.assoc, ← hm₂F, ← Category.assoc, ← Spec.map_comp]
    rfl

  have hcoe₁ : ∀ b : ↥(IgusaScheme.chartAlgFin M q),
      (((ιF₁ b : ↥(IgusaScheme.chartAlgFin (M * ℓ) q)) : ↥(modularFunctionFieldFull (M * ℓ))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ) := fun b => by
    rw [hιF₁ b]; exact coe_φ₁ q M ℓ _
  have hcoe₂ : ∀ b : ↥(IgusaScheme.chartAlgFin M q),
      ((((ιFw.comp ιF₂) b : ↥(IgusaScheme.chartAlgFin (M * ℓ) q)) : ↥(modularFunctionFieldFull (M * ℓ))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ) := fun b => by
    rw [AlgHom.comp_apply, hιFw, hιF₂ b]; exact coe_φ₂ q M ℓ _
  exact ⟨π₁, π₂, hπ₁fin, hπ₂fin, hπ₁lfp, hπ₂lfp, ιF₁, ιFw.comp ιF₂, hm₁surj, hπ₂surj, hcoe₁, hcoe₂, hpin₁, hpin₂⟩

end
end S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair (solution)
