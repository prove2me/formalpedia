-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/861ad6ac-c5ed-5b0b-9a0f-84b72eb92597

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
import Theorems.Thm_ModularCurve_exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_nonempty_iso_twoChartIntegralModel
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open ModularCurve ModularCurve.IgusaScheme

namespace IgusaALInvol

theorem isDominant_ιFin (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] : IsDominant (TwoChartIntegralModel.ιFin R F j) := by
  haveI : Nonempty (XFin R F j) := inferInstanceAs (Nonempty (PrimeSpectrum (TwoChartIntegralModel.chartAlgFin R F j)))
  refine ⟨?_⟩
  show Dense (Set.range (TwoChartIntegralModel.ιFin R F j).base)
  exact (TwoChartIntegralModel.ιFin R F j).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

theorem hom_ext_of_ιFin_comp_eq (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    {Y Z : Scheme.{u}} (f g : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Y) (q : Y ⟶ Z) [IsSeparated q]
    (h : f ≫ q = g ≫ q) (hFin : TwoChartIntegralModel.ιFin R F j ≫ f = TwoChartIntegralModel.ιFin R F j ≫ g) : f = g := by
  haveI := isDominant_ιFin R F j
  exact ext_of_isDominant_of_isSeparated q h (TwoChartIntegralModel.ιFin R F j) hFin

theorem isIntegral_adjoin_map {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (σ : A →ₐ[R] A) (s x : A)
    (hx : IsIntegral (Algebra.adjoin R ({s} : Set A)) x) :
    IsIntegral (Algebra.adjoin R ({σ s} : Set A)) (σ x) := by
  have hmap : (Algebra.adjoin R ({s} : Set A)).map σ = Algebra.adjoin R ({σ s} : Set A) := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : ↥(Algebra.adjoin R ({s} : Set A)) →+* ↥(Algebra.adjoin R ({σ s} : Set A)) :=
    ((σ.comp (Algebra.adjoin R ({s} : Set A)).val).codRestrict (Algebra.adjoin R ({σ s} : Set A))
      (fun y => by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨y, y.2, rfl⟩)).toRingHom
  exact hx.map_of_comp_eq φ σ.toRingHom (by ext; rfl)

section Main

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull (N * p))

abbrev σ : FF ≃ₐ[ℤp] FF := (atkinLehnerInvolutionFull N p).restrictScalars ℤp

theorem σ_apply (x : FF) : σ N p x = atkinLehnerInvolutionFull N p x := rfl

theorem main (hpN : ¬ p ∣ N) :
    ∃ (w : ModularCurve.IgusaScheme (N * p) p ≅ ModularCurve.IgusaScheme (N * p) p)
      (theta : ↥(IgusaScheme.chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(IgusaScheme.chartAlgFin (N * p) p)),
      w.hom ≫ igusaTo (N * p) p = igusaTo (N * p) p ∧
      w.hom ≫ w.hom = 𝟙 _ ∧
      (∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N * p) p)) : FF) = atkinLehnerInvolutionFull N p (b : FF)) ∧
      IgusaScheme.ιFin (N * p) p ≫ w.hom =
        Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N * p) p := by
  classical

  obtain ⟨theta, htheta, hthth⟩ := exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull N p hpN

  let j' : FF := σ N p (jFull (N * p))
  have hσσ : ∀ x : FF, σ N p (σ N p x) = x := fun x => atkinLehnerInvolutionFull_apply_apply N p hpN x
  have hσj : σ N p (jFull (N * p)) = j' := rfl
  have hσj' : σ N p j' = (jFull (N * p)) := hσσ (jFull (N * p))
  have hj'0 : j' ≠ 0 := fun h0 => jFull_ne_zero (N * p) (by
    have := congrArg (σ N p) h0
    rwa [hσj', map_zero] at this)
  haveI : Fact (j' ≠ 0) := ⟨hj'0⟩

  obtain ⟨t, eFin, eInf, heFin, heInf, ht_over, ht_fin, ht_inf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq ℤp FF FF (jFull (N * p)) j' (σ N p) hσj
  obtain ⟨t', eFin', eInf', heFin', heInf', -, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq ℤp FF FF j' (jFull (N * p)) (σ N p) hσj'

  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel ℤp FF (jFull (N * p))) := TwoChartIntegralModel.isIntegral ℤp FF (jFull (N * p))
  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel ℤp FF j') := TwoChartIntegralModel.isIntegral ℤp FF j'
  obtain ⟨hftF, hftI⟩ := IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (N * p) p
  haveI : Algebra.FiniteType ℤp ↥(TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p))) := hftF
  haveI : Algebra.FiniteType ℤp ↥(TwoChartIntegralModel.chartAlgInf ℤp FF (jFull (N * p))) := hftI
  haveI : Algebra.FiniteType ℤp ↥(TwoChartIntegralModel.chartAlgInf ℤp FF j') := by
    refine (inferInstance : Algebra.FiniteType ℤp ↥(TwoChartIntegralModel.chartAlgInf ℤp FF (jFull (N * p)))).of_surjective eInf
      (fun y => ⟨eInf' y, Subtype.ext ?_⟩)
    have h1 := heInf (eInf' y)
    rw [heInf', hσσ] at h1
    exact h1
  haveI : IsDiscreteValuationRing ℤp := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsNoetherianRing ℤp := inferInstance
  haveI : IsProper (toBase ℤp FF (jFull (N * p))) := TwoChartIntegralModel.isProper_toBase ℤp FF (jFull (N * p))
  haveI : IsSeparated (toBase ℤp FF (jFull (N * p))) := inferInstance
  haveI : IsSeparated (toBase ℤp FF j') := by
    have e : toBase ℤp FF j' = t.inv ≫ toBase ℤp FF (jFull (N * p)) := by rw [← ht_over, Iso.inv_hom_id_assoc]
    rw [e]; infer_instance

  have hfin : j' ∈ TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p)) := by
    have h := (theta (IgusaScheme.jChartFin (N * p) p)).2
    have hv : ((theta (IgusaScheme.jChartFin (N * p) p) : ↥(IgusaScheme.chartAlgFin (N * p) p)) : FF) = j' := by
      rw [htheta, IgusaScheme.coe_jChartFin]; rfl
    rw [hv] at h
    exact h
  have hfin' : (jFull (N * p)) ∈ TwoChartIntegralModel.chartAlgFin ℤp FF j' := by
    have h := (eFin ⟨j', hfin⟩).2
    rw [heFin] at h
    change σ N p j' ∈ TwoChartIntegralModel.chartAlgFin ℤp FF j' at h
    rwa [hσj'] at h

  have hb : ∃ a ∈ Algebra.adjoin ℤp ({(jFull (N * p))⁻¹} : Set FF),
      IsIntegral (Algebra.adjoin ℤp ({(jFull (N * p))⁻¹} : Set FF)) ((1 + (jFull (N * p))⁻¹ * a) * j'⁻¹) :=
    exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull N p hpN ℤp
  have hb' : ∃ a ∈ Algebra.adjoin ℤp ({j'⁻¹} : Set FF),
      IsIntegral (Algebra.adjoin ℤp ({j'⁻¹} : Set FF)) ((1 + j'⁻¹ * a) * (jFull (N * p))⁻¹) := by
    obtain ⟨a, ha, hint⟩ := hb
    refine ⟨σ N p a, ?_, ?_⟩
    · have : (Algebra.adjoin ℤp ({(jFull (N * p))⁻¹} : Set FF)).map (σ N p : FF →ₐ[ℤp] FF) = Algebra.adjoin ℤp ({j'⁻¹} : Set FF) := by
        rw [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_algHom, map_inv₀, hσj]
      rw [← this]
      exact Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    · have h := isIntegral_adjoin_map (σ N p : FF →ₐ[ℤp] FF) (jFull (N * p))⁻¹ _ hint
      rw [AlgEquiv.coe_algHom, map_inv₀, hσj] at h
      have e : σ N p ((1 + (jFull (N * p))⁻¹ * a) * j'⁻¹) = (1 + j'⁻¹ * σ N p a) * (jFull (N * p))⁻¹ := by
        rw [map_mul, map_add, map_one, map_mul, map_inv₀, map_inv₀, hσj, hσj']
      rwa [e] at h
  have hvis := AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
    ℤp FF (jFull (N * p)) j' hb
  have hvis' := AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
    ℤp FF j' (jFull (N * p)) hb'

  obtain ⟨c, ιF, s, ψ, hιF, hιFbij, hs, hψ, hc_over, hc_fin, hc_inf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem ℤp FF (jFull (N * p)) j'
      hfin hfin' hvis hvis'

  let wT : AlgebraicCurve.TwoChartIntegralModel ℤp FF (jFull (N * p)) ≅ AlgebraicCurve.TwoChartIntegralModel ℤp FF (jFull (N * p)) := c ≪≫ t.symm
  have hT_over : wT.hom ≫ toBase ℤp FF (jFull (N * p)) = toBase ℤp FF (jFull (N * p)) := by
    show (c.hom ≫ t.inv) ≫ toBase ℤp FF (jFull (N * p)) = toBase ℤp FF (jFull (N * p))
    have htinv : t.inv ≫ toBase ℤp FF (jFull (N * p)) = toBase ℤp FF j' := by rw [← ht_over, Iso.inv_hom_id_assoc]
    rw [Category.assoc, htinv, hc_over]
  let θT : ↥(TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p))) →ₐ[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p))) :=
    ιF.comp eFin
  have hθval : ∀ x, ((θT x : ↥(TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p)))) : FF) = σ N p x := by
    intro x
    show ((ιF (eFin x) : ↥(TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p)))) : FF) = σ N p x
    rw [hιF, heFin]
  have hθθ : θT.comp θT = AlgHom.id ℤp _ := by
    ext x
    rw [AlgHom.comp_apply, hθval, hθval, hσσ]
    rfl
  have hT_fin : TwoChartIntegralModel.ιFin ℤp FF (jFull (N * p)) ≫ wT.hom =
      Spec.map (CommRingCat.ofHom θT.toRingHom) ≫ TwoChartIntegralModel.ιFin ℤp FF (jFull (N * p)) := by
    show TwoChartIntegralModel.ιFin ℤp FF (jFull (N * p)) ≫ (c.hom ≫ t.inv) = _
    rw [← Category.assoc, hc_fin, Category.assoc, ← ht_fin, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hT_invol : wT.hom ≫ wT.hom = 𝟙 _ := by
    refine hom_ext_of_ιFin_comp_eq ℤp FF (jFull (N * p)) (wT.hom ≫ wT.hom) (𝟙 _) (toBase ℤp FF (jFull (N * p)))
      (by rw [Category.assoc, hT_over, hT_over, Category.id_comp]) ?_
    rw [Category.comp_id, ← Category.assoc, hT_fin, Category.assoc, hT_fin, ← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom θT.toRingHom ≫ CommRingCat.ofHom θT.toRingHom = 𝟙 _ := by
      rw [← CommRingCat.ofHom_comp]
      change CommRingCat.ofHom (θT.comp θT).toRingHom = _
      rw [hθθ]
      rfl
    rw [this, Spec.map_id, Category.id_comp]

  have hθeq : CommRingCat.ofHom theta.toRingEquiv.toRingHom = CommRingCat.ofHom θT.toRingHom := by
    congr 1
    refine RingHom.ext fun x => Subtype.ext ?_
    show ((theta x : ↥(IgusaScheme.chartAlgFin (N * p) p)) : FF) = ((θT x : ↥(TwoChartIntegralModel.chartAlgFin ℤp FF (jFull (N * p)))) : FF)
    rw [htheta, hθval]
    rfl

  obtain ⟨e, he_over, he_fin, -⟩ := IgusaScheme.nonempty_iso_twoChartIntegralModel (N * p) p
  have he_inv : e.inv ≫ igusaTo (N * p) p = toBase ℤp FF (jFull (N * p)) := by rw [← he_over, Iso.inv_hom_id_assoc]
  let w : ModularCurve.IgusaScheme (N * p) p ≅ ModularCurve.IgusaScheme (N * p) p := e ≪≫ wT ≪≫ e.symm
  refine ⟨w, theta, ?_, ?_, htheta, ?_⟩
  · show (e.hom ≫ wT.hom ≫ e.inv) ≫ igusaTo (N * p) p = igusaTo (N * p) p
    rw [Category.assoc, Category.assoc, he_inv, hT_over, he_over]
  · show (e.hom ≫ wT.hom ≫ e.inv) ≫ (e.hom ≫ wT.hom ≫ e.inv) = 𝟙 _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hT_invol, Iso.hom_inv_id]
  ·

    show IgusaScheme.ιFin (N * p) p ≫ (e.hom ≫ wT.hom ≫ e.inv) = _
    rw [← cancel_mono e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% he_fin, he_fin, hθeq]
    exact hT_fin

end Main

end IgusaALInvol

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ∃ (w : ModularCurve.IgusaScheme (N * p) p ≅ ModularCurve.IgusaScheme (N * p) p)
      (theta : ↥(IgusaScheme.chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(IgusaScheme.chartAlgFin (N * p) p)),
      w.hom ≫ igusaTo (N * p) p = igusaTo (N * p) p ∧
      w.hom ≫ w.hom = 𝟙 _ ∧
      (∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
        atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p)))) ∧
      IgusaScheme.ιFin (N * p) p ≫ w.hom =
        Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N * p) p :=
  IgusaALInvol.main N p hpN

end
end S_ModularCurve_IgusaScheme_exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd (solution)
