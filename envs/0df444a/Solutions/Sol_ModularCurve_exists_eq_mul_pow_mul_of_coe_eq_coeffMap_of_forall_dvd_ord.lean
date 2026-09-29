-- Prove2me | solution 1 for ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/953fab6d-c088-5bdf-a61b-148df223219d

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_essFiniteType_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Theorems.Thm_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord
import Theorems.Thm_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed
import Theorems.Thm_AlgebraicCurve_inv_smul_D_eq_zero_iff_exists_pow_eq
import Theorems.Thm_AlgebraicCurve_exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open scoped MatrixGroups

namespace MultDescentReduce

open KaehlerDifferential

theorem cartier_dlog_fixed {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) (hp1 : 1 ≤ p)
    (C : Ω[L⁄K] →+ Ω[L⁄K]) (hsemi : ∀ (f : L) (ω : Ω[L⁄K]), C (f ^ p • ω) = f • C ω)
    (hlog : ∀ f : L, C (f ^ (p - 1) • D K L f) = D K L f) (f : L) (hf : f ≠ 0) :
    C (f⁻¹ • D K L f) = f⁻¹ • D K L f := by
  have hpow : f⁻¹ = (f⁻¹) ^ p * f ^ (p - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp1).symm⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm ((f⁻¹) ^ m) f⁻¹, mul_assoc, ← mul_pow, inv_mul_cancel₀ hf,
      one_pow, mul_one]
  conv_lhs => rw [hpow, ← smul_smul]
  rw [hsemi, hlog]

theorem map_dlog {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    (x : F) :
    KaehlerDifferential.map K K' F F' (x⁻¹ • D K F x) = (algebraMap F F' x)⁻¹ • D K' F' (algebraMap F F' x) := by
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, ← algebraMap_smul F' x⁻¹, map_inv₀]

theorem dlog_mul_inv_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L] (a b : L) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a⁻¹ • D K L a = b⁻¹ • D K L b) : (a * b⁻¹)⁻¹ • D K L (a * b⁻¹) = 0 := by
  have key : (a * b⁻¹)⁻¹ • D K L (a * b⁻¹) = a⁻¹ • D K L a - b⁻¹ • D K L b := by
    rw [Derivation.leibniz, Derivation.leibniz_inv, smul_add, smul_smul, smul_smul, smul_smul, sub_eq_add_neg, add_comm,
      ← neg_smul]
    congr 1
    · congr 1
      field_simp
    · congr 1
      field_simp
  rw [key, h, sub_self]

end MultDescentReduce

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra κ K] :
    ∀ f : ModularCurve.qExpFunctionFieldC K Γ, f ≠ 0 →
      (∀ v : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ), (p : ℤ) ∣ v.ord f) →
      ∃ (f₀ : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f₁ : ModularCurve.qExpFunctionFieldC K Γ) (c : K) (g : ModularCurve.qExpFunctionFieldC K Γ),
        f₀ ≠ 0 ∧ c ≠ 0 ∧
        (∀ v₀ : AlgebraicCurve.Place κ (↥(ModularCurve.qExpFunctionFieldC κ Γ)), (p : ℤ) ∣ v₀.ord f₀) ∧
        ((f₁ : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) ((f₀ : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) : LaurentSeries κ) ∧
        f = algebraMap K (ModularCurve.qExpFunctionFieldC K Γ) c * g ^ p * f₁ := by
  intro f hf hdiv
  have hp : Nat.Prime p := Fact.out

  have iMK : MulAction K (LaurentSeries K) := inferInstance
  have iMκ : MulAction κ (LaurentSeries κ) := inferInstance
  have iModK : Module K (LaurentSeries K) := inferInstance
  have iModκ : Module κ (LaurentSeries κ) := inferInstance
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap κ K).injective p
  haveI : Algebra.EssFiniteType κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) := ModularCurve.essFiniteType_qExpFunctionFieldC_of_isAlgClosed κ Γ hT
  haveI : AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ Γ hT
  haveI : Algebra.EssFiniteType K ↥(ModularCurve.qExpFunctionFieldC K Γ) := ModularCurve.essFiniteType_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : ∀ w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), w.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := κ) (F := ↥(ModularCurve.qExpFunctionFieldC κ Γ)) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : CharP ↥(ModularCurve.qExpFunctionFieldC κ Γ) p := charP_of_injective_algebraMap (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)).injective p
  haveI : CharP ↥(ModularCurve.qExpFunctionFieldC K Γ) p := charP_of_injective_algebraMap (algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ)).injective p
  have hland : ∀ z : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ModularCurve.coeffMap (algebraMap κ K) (z : LaurentSeries κ) ∈ ModularCurve.qExpFunctionFieldC K Γ := by
    intro z
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC κ K Γ]
    exact IntermediateField.subset_adjoin K _ ⟨z, z.2, rfl⟩
  let e : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    ((ModularCurve.coeffMap (algebraMap κ K)).comp (ModularCurve.qExpFunctionFieldC κ Γ).val.toRingHom).codRestrict
      (ModularCurve.qExpFunctionFieldC K Γ) hland
  letI : Algebra ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := e.toAlgebra
  have he : ∀ z : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ((e z : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (z : LaurentSeries κ) :=
    fun z => rfl
  letI : Algebra κ ↥(ModularCurve.qExpFunctionFieldC K Γ) := ((algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ)).comp (algebraMap κ K)).toAlgebra
  haveI : IsScalarTower κ K ↥(ModularCurve.qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    apply Subtype.ext
    change algebraMap K (LaurentSeries K) (algebraMap κ K a) =
      ModularCurve.coeffMap (algebraMap κ K) (algebraMap κ (LaurentSeries κ) a)
    rw [ModularCurve.algebraMap_laurentSeries_eq_single K, ModularCurve.algebraMap_laurentSeries_eq_single κ,
      ModularCurve.coeffMap_single]
  haveI : SMulCommClass K ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    ⟨fun a b c => by rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]; ring⟩
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hle : ModularCurve.qExpFunctionFieldC K Γ ≤
        (IntermediateField.adjoin K (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)))).map (ModularCurve.qExpFunctionFieldC K Γ).val := by
      refine le_trans (le_of_eq (ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC κ K Γ)) ?_
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨u, hu, rfl⟩
      rw [IntermediateField.coe_map]
      exact ⟨algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) ⟨u, hu⟩, IntermediateField.subset_adjoin K _ ⟨⟨u, hu⟩, rfl⟩, he ⟨u, hu⟩⟩
    have hz : (z : LaurentSeries K) ∈
        (((IntermediateField.adjoin K (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)))).map (ModularCurve.qExpFunctionFieldC K Γ).val :
          IntermediateField K (LaurentSeries K)) : Set (LaurentSeries K)) := hle z.2
    rw [IntermediateField.coe_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    rwa [← Subtype.ext hwz]

  obtain ⟨xκ, -, hxκtr, hxκfin⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ Γ hT
  obtain ⟨xK, -, hxKtr, hxKfin⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI := hxκfin
  haveI := hxKfin
  obtain ⟨C, ⟨hsemi, hker, hlog⟩, -⟩ := AlgebraicCurve.cartierOperator_existsUnique (K := κ) p xκ
  obtain ⟨C', ⟨hsemi', hker', hlog'⟩, -⟩ := AlgebraicCurve.cartierOperator_existsUnique (K := K) p xK

  have hreg := AlgebraicCurve.dlog_mem_regularDifferentials_of_forall_dvd_ord K ↥(ModularCurve.qExpFunctionFieldC K Γ) p hf hdiv
  have hfix := MultDescentReduce.cartier_dlog_fixed p hp.one_le C' hsemi' hlog' f hf

  obtain ⟨ω, hωreg, hωfix, hωmap⟩ :=
    AlgebraicCurve.exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
      κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) K ↥(ModularCurve.qExpFunctionFieldC K Γ) p ⟨xκ, hxκtr, hxκfin⟩ ⟨xK, hxKtr, hxKfin⟩ hgen C hsemi hker hlog C' hsemi' hker' hlog' _ hreg hfix

  obtain ⟨f₀, hf₀, hωf₀⟩ := AlgebraicCurve.exists_dlog_of_cartierOperator_fixed (K := κ) p xκ C hsemi hker hlog ω hωfix
  have hf₁ : algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) f₀ ≠ 0 := (map_ne_zero _).mpr hf₀

  rw [hωf₀, MultDescentReduce.map_dlog] at hωmap
  obtain ⟨g, hg⟩ := (AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq p _ (mul_ne_zero hf (inv_ne_zero hf₁))).mp
    (MultDescentReduce.dlog_mul_inv_eq_zero f _ hf hf₁ hωmap.symm)

  have hdiv₀ : ∀ v₀ : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), (p : ℤ) ∣ v₀.ord f₀ := by
    intro v
    obtain ⟨a, ha, hωa⟩ := AlgebraicCurve.mem_regularDifferentials_iff.mp hωreg v
    have h0 : v.HasSimpleResidue ω 0 := by
      rw [hωa]; exact AlgebraicCurve.Place.hasSimpleResidue_zero_of_mem ha
    have h1 : v.HasSimpleResidue ω ((v.ord f₀ : ℤ) : κ) := by
      rw [hωf₀]; exact (AlgebraicCurve.Place.hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord f₀ hf₀ v).2
    have hz : ((v.ord f₀ : ℤ) : κ) = 0 :=
      (AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt v _ h0.hasSimplePoleAt).unique h1 h0
    exact (CharP.intCast_eq_zero_iff κ p _).mp hz
  refine ⟨f₀, algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) f₀, 1, g, hf₀, one_ne_zero, hdiv₀, he f₀, ?_⟩
  rw [map_one, one_mul, hg, mul_assoc, inv_mul_cancel₀ hf₁, mul_one]

end S_ModularCurve_exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord
end P2MW
export P2MW.S_ModularCurve_exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord (solution)
