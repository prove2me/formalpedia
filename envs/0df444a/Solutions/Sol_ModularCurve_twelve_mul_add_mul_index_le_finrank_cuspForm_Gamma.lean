-- Prove2me | solution 1 for ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7822693f-5d9a-5f3b-b197-3a40faae9ac8

import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Theorems.Thm_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF
import Theorems.Thm_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "LevelN.ring LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.twelve_mul_add_mul_index_le_genusFF LevelN.exists_linearMap_regularDifferentials_cuspForm_injective"
namespace GenusBoundAssembly
p2m_open "ModularCurve"

open AlgebraicCurve ModularCurve.LevelN

section Bridge

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

theorem curve_package {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F)
      (_ : ∀ w : Place K F, w.DCoordGenerates),
      Module.Finite K ↥(regularDifferentials K F) ∧
        genusFF K F = Module.finrank K ↥(regularDifferentials K F) := by
  classical
  obtain ⟨t, ht, htfd, htsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField htr hfd
  haveI := htfd
  haveI := htsep
  haveI hC1 : IsCurveOver K F := isCurveOver_of_transcendental ht htfd htsep
  haveI hC2 : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional ht htfd
  haveI : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI hC3 : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  letI : Algebra (RatFunc K) F := ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch K F := by
    unfold FunctionFieldRiemannRoch
    intro _ _ _ ω hω D
    exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed K F
  have hSG : StichtenothGenusExists K F := stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic K F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  have hg : genus K F = genusFF K F := genus_eq_genusFF hRR hWDA hC
  obtain ⟨hfin, hdim⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
  exact ⟨hC1, hC2, hC3, hfin, by rw [hdim, hg]⟩

end Bridge

theorem isDomain_ring (N : ℕ) [NeZero N] : IsDomain (ring N) := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  have hdom : ∀ a b : UpperHalfPlane → ℂ, a ∈ ring N → b ∈ ring N → a * b = 0 → a = 0 ∨ b = 0 :=
    h.2.2.2.2.2
  haveI : NoZeroDivisors (ring N) :=
    ⟨fun {a b} hab => by
      have h' := hdom (a : UpperHalfPlane → ℂ) b a.2 b.2 (by
        have := congrArg (Subtype.val) hab
        simpa using this)
      rcases h' with h' | h'
      · left; exact Subtype.ext h'
      · right; exact Subtype.ext h'⟩
  haveI : Nontrivial (ring N) := ⟨⟨0, 1, by
    intro h01
    have := congrArg (fun F : ring N => (F : UpperHalfPlane → ℂ) UpperHalfPlane.I) h01
    simp at this⟩⟩
  exact NoZeroDivisors.to_isDomain _

theorem main (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : IsDomain (ring N) := isDomain_ring N

  let K := FractionRing (ring N)

  obtain ⟨_, _, _, _, _, htr, hfd, _, _⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin N K

  have hgen := ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF N hN K

  obtain ⟨Φ, hΦ⟩ :=
    ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective N K

  obtain ⟨_, _, _, hfin, hg⟩ := curve_package (K := ℂ) (F := K) htr hfd
  haveI := hfin
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) :=
    CuspForm.finiteDimensional_of_isArithmetic _ 2
  have hle : Module.finrank ℂ ↥(regularDifferentials ℂ K) ≤
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) :=
    LinearMap.finrank_le_finrank_of_injective hΦ
  calc 12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
      ≤ 12 * N * genusFF ℂ K +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := hgen
    _ = 12 * N * Module.finrank ℂ ↥(regularDifferentials ℂ K) +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by rw [hg]
    _ ≤ 12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
        gcongr

end ModularCurve.GenusBoundAssembly

theorem solution (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
  ModularCurve.GenusBoundAssembly.main N hN

end S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma
end P2MW
export P2MW.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma (solution)
