-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/21f4d5e1-7ea4-5b47-9fcd-2b651b7c8fb0

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_finprod_sq_mul_lamSqArch_eq_one_of_forall_ne_zero_localZeta31_fe_rootNumber_of_isCubicInductionDataOn_of_archPackage_of_inv_eq_psiQ
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_mul_eq_finprod_rootNumber_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section PartA

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

namespace IDM

theorem subsingleton_algebra_ringOfIntegers_rat (A : Type) [Ring A] :
    Subsingleton (Algebra (𝓞 ℚ) A) := by
  refine ⟨fun P Q => Algebra.algebra_ext P Q fun r => ?_⟩
  have key : ∀ f g : 𝓞 ℚ →+* A, f = g := by
    intro f g
    refine RingHom.ext fun x => ?_
    have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) :=
      Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])
    rw [hx, map_intCast, map_intCast]
  exact RingHom.congr_fun (key (@algebraMap (𝓞 ℚ) A _ _ P) (@algebraMap (𝓞 ℚ) A _ _ Q)) r

theorem primeFibre_finite (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 ℚ)) :
    (primeFibre ℚ K p).Finite := by
  have hfin : (Ideal.primesOver p.asIdeal (𝓞 K)).Finite :=
    IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
  refine (hfin.preimage (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  intro 𝔓 h𝔓
  rw [mem_primeFibre] at h𝔓
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h𝔓]
  rfl

theorem primeFibre_nonempty (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K p := by
  have hfund := Ideal.sum_ramification_inertia (𝓞 K) ℚ K p.ne_bot
  have hne : (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hfund
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  obtain ⟨P, hP⟩ := hne
  have hP' := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 K)).mp hP
  refine ⟨⟨P, hP'.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨hP'.1, hP'.2⟩⟩, ?_⟩
  rw [mem_primeFibre]
  exact HeightOneSpectrum.ext hP'.2.over.symm

theorem not_isUnramifiedCharAt_of_hasConductorExponentAt_of_pos
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (a : ℕ) (ha : 0 < a) (h : HasConductorExponentAt K 𝔓 (localChar χ 𝔓) a) :
    ¬ IsUnramifiedCharAt χ 𝔓 := by
  intro hunr
  obtain ⟨u, hu, hne⟩ := h.2 (a - 1) (Nat.sub_lt ha Nat.one_pos)
  have hu1 : Valued.v (u : 𝔓.adicCompletion K) = 1 := ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff K 𝔓).mp hu).1
  have hu2 : Valued.v (((u⁻¹ : (𝔓.adicCompletion K)ˣ) : 𝔓.adicCompletion K)) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]
  refine hne (hunr u ?_ ?_)
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu1.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu2.le

theorem isBadPlace_of_one_le_conductorExponentAt
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμc : Continuous μ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hdeep : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = p →
      1 ≤ LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓)) :
    IsBadPlace K μ p := by
  obtain ⟨𝔓, h𝔓⟩ := primeFibre_nonempty K p
  refine Or.inr ⟨𝔓, h𝔓, ?_⟩
  obtain ⟨n, hn⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K 𝔓 (localChar μ 𝔓)
    (NumberField.TateGlobal.continuous_localChar μ hμc 𝔓)
  have h1 := hdeep 𝔓 ((mem_primeFibre ℚ p 𝔓).mp h𝔓)
  rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K 𝔓 hn] at h1
  exact not_isUnramifiedCharAt_of_hasConductorExponentAt_of_pos K μ 𝔓 n h1 hn

theorem exists_mul_adelicBox_toReal_eq_one :
    ∃ c : ℂ, c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1 := by
  have hpos := adelicAddHaar_adelicBox_pos ℚ
  have hlt := adelicAddHaar_adelicBox_lt_top ℚ
  have hne : ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos hpos.ne' hlt.ne).ne'
  exact ⟨_, inv_mul_cancel₀ hne⟩

open scoped Classical in

theorem finprod_primeFibre_cpow_zpow_eq_cpow (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (pe : HeightOneSpectrum (𝓞 K) → ℤ) (ℓ : ℕ)
    (hℓ : (ℓ : ℤ) = ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓) (s : ℂ) :
    ∏ᶠ 𝔓 ∈ primeFibre ℚ K v, ((((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (pe 𝔓)) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) := by
  have hfin := primeFibre_finite K v
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ideal.absNorm_eq_zero_iff.ne]
    exact v.ne_bot

  have hfac : ∀ 𝔓 ∈ primeFibre ℚ K v,
      ((((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (pe 𝔓)) =
        (Ideal.absNorm v.asIdeal : ℂ) ^ (((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓 : ℤ) * ((1 : ℂ) / 2 - s)) := by
    intro 𝔓 h𝔓
    have h : 𝔓.under (𝓞 ℚ) = v := (mem_primeFibre ℚ v 𝔓).mp h𝔓
    haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal v.asIdeal v.isPrime v.ne_bot, Nat.cast_pow]
    symm
    rw [show ((((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) * pe 𝔓 : ℤ) : ℂ) * ((1 : ℂ) / 2 - s)) =
        (pe 𝔓 : ℂ) * ((v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℕ) * ((1 : ℂ) / 2 - s)) by push_cast; ring,
      Complex.cpow_int_mul,
      Complex.cpow_nat_mul' (by rw [Complex.natCast_arg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos)
        (by rw [Complex.natCast_arg, mul_zero]; exact Real.pi_pos.le)]
  rw [finprod_mem_congr rfl hfac, finprod_mem_eq_finite_toFinset_prod _ hfin]
  rw [show ((ℓ : ℂ)) = ((ℓ : ℤ) : ℂ) by push_cast; rfl, hℓ, finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [Finset.sum_mul]

  induction hfin.toFinset using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.prod_insert haT, Finset.sum_insert haT, Complex.cpow_add _ _ hN0, ih]

end IDM

end PartA

section PartA2

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel

namespace IDM

theorem exists_nat_cast_eq_finsum_pinnedExp (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ℓ : ℕ, (ℓ : ℤ) = ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K χ 𝔓 := by
  have hnn : 0 ≤ ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
      LanglandsTunnell.Converse.pinnedExp K χ 𝔓 := by
    refine finsum_mem_induction (fun x : ℤ => 0 ≤ x) le_rfl (fun _ _ hx hy => add_nonneg hx hy) ?_
    intro 𝔓 _
    refine mul_nonneg (Int.natCast_nonneg _) ?_
    unfold LanglandsTunnell.Converse.pinnedExp
    refine add_nonneg (Int.natCast_nonneg _) ?_
    have h := LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K 𝔓
    have h2 := FractionalIdeal.count_coe_nonneg K 𝔓 (differentIdeal ℤ (𝓞 K))
    rw [← h] at h2
    exact h2
  exact ⟨_, (Int.toNat_of_nonneg hnn)⟩

theorem inducedEulerPoly_ne_zero (K : Type) [Field K] [NumberField K]
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    inducedEulerPoly ℚ c v ≠ 0 := by
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  have hev : (inducedEulerPoly ℚ c v).eval 0 = 1 := by
    unfold inducedEulerPoly
    refine finprod_mem_induction (fun P : Polynomial ℂ => P.eval 0 = 1) (by simp)
      (fun P Q hP hQ => by rw [Polynomial.eval_mul, hP, hQ, one_mul]) ?_
    intro 𝔓 _
    unfold inducedFactor
    haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
    have hf : 0 < (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := Ideal.inertiaDeg'_pos _ _
    show Polynomial.eval 0 _ = 1
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_C,
      Polynomial.eval_X, zero_pow hf.ne', mul_zero, sub_zero]
  intro h
  rw [h, Polynomial.eval_zero] at hev
  exact zero_ne_one hev

theorem not_isRamifiedIn_of_forall_ramificationIdx_eq_one (K : Type) [Field K] [NumberField K]
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ SQ) : ¬ IsRamifiedIn K v := by
  rintro ⟨𝔓, h𝔓, hne⟩
  rw [mem_primeFibre] at h𝔓
  apply hne
  rw [← h𝔓]
  exact hSQ 𝔓 (h𝔓 ▸ hv)

theorem apply_neg_one_eq_one_or (G : Type) [Monoid G] [HasDistribNeg G] (η : G →* ℂˣ) :
    ((η (-1) : ℂˣ) : ℂ) = 1 ∨ ((η (-1) : ℂˣ) : ℂ) = -1 := by
  have h : η (-1) * η (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have h2 : ((η (-1) : ℂˣ) : ℂ) * ((η (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, h, Units.val_one]
  exact mul_self_eq_one_iff.mp h2

end IDM

end PartA2

open IDM in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)

    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdeep : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ SQ →
      1 ≤ LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω₃ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω₃ (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((ω₃ (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)

    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ μ
      {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} X)
    (hX0 : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hX1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w → X.whittakerLoc w 1 = 1)
    (hXc : Continuous X.form) (hXw : Continuous X.whittaker) (hXdw : Continuous X.dualWhittaker)
    (hXg : IsGaugeMajorised3 ℚ X.whittaker) (hXdg : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hArchEq : X.whittakerArch = Warch)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
            X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (hadm : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h) :
    ∃ lamM : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → lamM v = 1) ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lamM v ^ 2) * lamSqArch K = 1 ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc p), ∀ b : ℕ,
            (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA p = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 p,
              letI := LanglandsTunnell.TateLocal.localBorel ℚ p
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)))
                  W η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) W η s g *
                    Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) (dualWhittakerFn3 W) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)
                    W η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lamM p *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))))) ∧

      (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → v ∉ SQ → ¬ IsRamifiedIn K v →
        psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
        ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v),
        (∀ g : LocalGL3 v,
          (letI := localBorel ℚ v
           ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
            (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
              P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
            IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
                ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
            IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                  W 1 (1 - s) g =
                ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
                  (((lamM v *
                      ((∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
                        ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w))) *
                      (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s))) * P s)))) := by
  classical
  haveI := IDM.subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _

  subst hArchEq

  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v}.Finite :=
    LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous K μ hμ.2.1
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset with hSdef
  have hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S := fun w => by
    rw [hSdef, Set.Finite.mem_toFinset]; rfl
  have hSeq : ((S : Set (HeightOneSpectrum (𝓞 ℚ)))) = {v | IsBadPlace K μ v} :=
    Set.ext fun w => (Finset.mem_coe.trans (hSbad w).symm)
  have hXS : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X := by rw [hSeq]; exact hX

  obtain ⟨c, hc⟩ := IDM.exists_mul_adelicBox_toReal_eq_one
  have hlevS : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 := fun v _ => hlev v
  have hψS : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0 := fun w _ => hlev w
  have hψinvAll : ∀ v : HeightOneSpectrum (𝓞 ℚ), psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ := by
    intro v
    have hψ' : ψ = NumberField.StandardAddChar.psiQ⁻¹ := by rw [← hψQ, inv_inv]
    ext x
    rw [AddChar.inv_apply, NumberField.StandardAddChar.psiLocal_rat_eq_psiQ_adeleSingleAt, map_neg, hψ']
    show NumberField.StandardAddChar.psiQ⁻¹ (NumberField.StandardAddChar.adeleSingleAt ℚ v x) = _
    rw [AddChar.inv_apply]
  have h1S : ∀ w ∈ S, X.whittakerLoc w 1 = 1 := fun w hw => hX1 w ((hSbad w).mpr hw)
  have hadmS : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) :=
    fun w hw => hadm w ((hSbad w).mpr hw)
  have hcentS : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h :=
    fun w hw => hcent w ((hSbad w).mpr hw)
  have hne : X.whittakerArch ≠ 0 := hWarch.1
  have hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)) := by
    intro w hw
    have hb := (hSbad w).mpr hw
    obtain ⟨hU, hirr⟩ := hBad {w}
    exact ⟨hX1 w hb, hirr w (Finset.mem_singleton_self w) hb, hU w (Finset.mem_singleton_self w) hb, hadm w hb⟩

  have hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a :=
    fun v hKv => LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
      K _hdeg ψ μ hμ _ X hX hXc hX0.1 v hKv

  have hcen : ∀ z : (InfiniteAdeleRing ℚ)ˣ, ((ω₃ (E z) : ℂˣ) : ℂ) = ((X.centralChar (E z) : ℂˣ) : ℂ) := by
    intro z
    obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
    have h1' := hWarch.2.2.2.2.1 z g
    have h2' := LanglandsTunnell.CubicInduction.whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
      K ψ μ _ S X hXS h1S E hE z g
    exact mul_right_cancel₀ hg (h1'.symm.trans h2')
  have hArchX := hWarch.2.2
  simp only [hcen] at hArchX

  obtain ⟨hS, hS'⟩ :=
    LanglandsTunnell.CubicInduction.sPart_integrable_and_dual_of_isCubicInductionDataOn_of_isGaugeMajorised3
      K _hdeg ψ hψ μ hμ uR aR uC kC hcR hcC hlev hoff D U gen S hSbad X hXS hXc hXw hXdw hXg hXdg hne hatS hcentS
      hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArchX
  have heven :=
    LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_of_isCubicInductionDataOn
      K _hdeg ψ hψ μ hμ uR aR uC kC hcR hcC hlev hoff D U gen S hSbad X hXS hXc hXw hXdw hXg hXdg hne hatS hcentS
      hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArchX
  have hodd :=
    LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
      K _hdeg ψ hψ μ hμ uR aR uC kC hcR hcC hlev hoff D U gen S hSbad X hXS hXc hXw hXdw hXg hXdg hne hatS hcentS
      hωcond E hE a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add ν_mul hArchX
  have harchOf : ∀ u : ℂ, (u = 1 ∨ u = -1) →
      ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
        (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ u = (-1 : ℂ) ^ e) ∧
        ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0 := by
    rintro u (rfl | rfl)
    · obtain ⟨gInf, σ, hσ, ⟨t, e, hte, he⟩, hnv⟩ := heven
      exact ⟨gInf, σ, hσ, ⟨t, e, hte, he.symm⟩, hnv⟩
    · obtain ⟨gInf, σ, hσ, ⟨t, e, hte, he⟩, hnv⟩ := hodd
      exact ⟨gInf, σ, hσ, ⟨t, e, hte, he.symm⟩, hnv⟩

  have hSQbad : ∀ p ∈ SQ, IsBadPlace K μ p := fun p hp =>
    IDM.isBadPlace_of_one_le_conductorExponentAt K μ hμ.2.1 p (fun 𝔓 h𝔓 => hdeep 𝔓 (by rw [h𝔓]; exact hp))
  have hSQS : SQ ⊆ S := fun p hp => (hSbad p).mp (hSQbad p hp)

  have hdeepAll := fun (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ) =>
    LanglandsTunnell.CubicInduction.exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one
      K _hdeg ψ hψ μ hμ hlevS hoff D U gen S hSbad X hXS hXc hXg hXdg hXw hXdw c hc hX0 hBad p (hSQS hp)
      (fun w hw _ => h1S w hw) (h1S p (hSQS hp)) hadmS hcentS hψS hS hS' (hlev p) E hE ν_mul uR aR uC kC hcR hcC hψQ
      ω₃ hω₃ a ha aInf haInf
      psiInf hpsiInf hψinf ν_add hν_add X.whittakerArch hWarch rfl
  choose lamD hlamD0 hlamD using hdeepAll

  have htameAll : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S → v ∉ SQ → ∃ lam : ℂ,
      ∀ (R₁ R₂ : Polynomial ℂ) (m : ℤ), R₁ ≠ 0 → R₂ ≠ 0 →
      (∀ g : LocalGL3 v,
          letI := localBorel ℚ v
          ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
            IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
              v) 1 g σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 s g *
                Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
            IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
              ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) 1⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
            (∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (X.whittakerLoc v) 1 (1 - s) g *
                (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
              R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) →
      ∀ s : ℂ,
        R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) *
            (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          (lam * ((∏ᶠ w ∈ primeFibre ℚ K v, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)) *
            ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar μ w))) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s)) *
            (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    intro v hv hv'
    have hKv := IDM.not_isRamifiedIn_of_forall_ramificationIdx_eq_one K SQ hSQ v hv'
    obtain ⟨gInf, σ, hσ, ⟨t, e, hte, he⟩, hnv⟩ := harchOf 1 (Or.inl rfl)
    refine ⟨1, fun R₁ R₂ m hR₁ hR₂ hFE s => ?_⟩
    rw [one_mul]
    exact LanglandsTunnell.CubicInduction.eval_mul_eq_finprod_rootNumber_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
      K _hdeg ψ hψ μ hμ hlevS hoff D U gen S hSbad X hXS hXc hXg hXdg hXw hXdw c hc hX0 hBad v hv
      (fun w hw _ => h1S w hw) hadmS hcentS hψS hS hS' hKv (hlev v) (hψinvAll v) E hE ν_mul
      ⟨gInf, σ, hσ, ⟨t, e, hte, by rw [MonoidHom.one_apply, Units.val_one]; exact he⟩, hnv⟩ R₁ R₂ m hR₁ hR₂ hFE s
  choose lamT hlamT using htameAll

  let lamM : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v =>
    if h : v ∈ SQ then lamD v h else if h' : v ∈ S then lamT v h' h else 1
  have hlamM_deep : ∀ p (hp : p ∈ SQ), lamM p = lamD p hp := fun p hp => by
    simp only [lamM, dif_pos hp]
  have hlamM_tame : ∀ v (hv : v ∈ S) (hv' : v ∉ SQ), lamM v = lamT v hv hv' := fun v hv hv' => by
    simp only [lamM, dif_neg hv', dif_pos hv]
  have hlamM_off : ∀ v, v ∉ S → lamM v = 1 := fun v hv => by
    have hv' : v ∉ SQ := fun h => hv (hSQS h)
    simp only [lamM, dif_neg hv', dif_neg hv]
  refine ⟨lamM, ?_, ?_, ?_, ?_⟩

  · intro v hv
    exact hlamM_off v (fun h => hv ((hSbad v).mpr h))

  · refine LanglandsTunnell.CubicInduction.finprod_sq_mul_lamSqArch_eq_one_of_forall_ne_zero_localZeta31_fe_rootNumber_of_isCubicInductionDataOn_of_archPackage_of_inv_eq_psiQ
      K _hdeg ψ hψ μ hμ hlevS hoff D U gen S hSbad X hXS hXc hXg hXdg hXw hXdw c hc hX0 hBad h1S hadmS hcentS hψS hS hS'
      E hE ν_mul uR aR uC kC hcR hcC hψQ ω₃ hω₃ a ha aInf haInf psiInf hpsiInf hψinf ν_add hν_add X.whittakerArch hWarch rfl
      SQ hSQS hSQ hdeep lamM hlamM_off ?_ ?_
    · intro v hv _
      rw [hlamM_deep v hv]
      exact ⟨hlamD0 v hv, hlamD v hv⟩
    · intro v hv hv' _ R₁ R₂ m hR₁ hR₂ hFE s
      rw [hlamM_tame v hv hv']
      exact hlamT v hv hv' R₁ R₂ m hR₁ hR₂ hFE s

  · intro p hp W hW
    refine LanglandsTunnell.CubicInduction.localZeta31_identified_of_mem_gl3CyclicSubspace K μ p (X.whittakerLoc p)
      (lamM p) ?_ W hW
    intro b hb η cη hη hcη ηA hηA hloc hBC g
    obtain ⟨gInf, σ, hσ, hte, hnv⟩ := harchOf _ (IDM.apply_neg_one_eq_one_or _ η)
    obtain ⟨R₁, R₂, m, hR₁, hR₂, hFE⟩ :=
      LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel
        K _hdeg ψ hψ μ hμ hlevS hoff D U gen S hSbad X hXS hXc hXg hXdg hXw hXdw c hc hX0 hBad E hE ν_mul
        p (hSQS hp) (fun w hw _ => h1S w hw) hadmS hcentS hS hS' η ⟨cη, hη⟩ ⟨gInf, σ, hσ, hte, hnv⟩
    obtain ⟨ℓ, hℓ⟩ := IDM.exists_nat_cast_eq_finsum_pinnedExp K
      (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) p
    have hId := hlamD p hp η cη b hη hcη hb ηA hηA hloc hBC ℓ hℓ ⟨gInf, σ, hσ, hte, hnv⟩ R₁ R₂ m hR₁ hR₂ hFE
    obtain ⟨Q₁, Q₂, n, σ₀, σ₁, hQ₂, hc30, hZ, hc31, hZd⟩ := hFE g
    refine ⟨Q₁ * R₂, Q₂ * R₂, n, σ₀, σ₁, mul_ne_zero hQ₂ hR₂, hc30, ?_, hc31, ?_⟩
    · intro s hs
      rw [Polynomial.eval_mul, Polynomial.eval_mul, ← mul_assoc, hZ s hs]
      ring
    · intro s hs
      have hN0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero, Ideal.absNorm_eq_zero_iff.ne]
        exact p.ne_bot
      rw [hlamM_deep p hp, Polynomial.eval_mul, Polynomial.eval_mul, hZd s hs,
        finprod_mem_mul_distrib (IDM.primeFibre_finite K p),
        IDM.finprod_primeFibre_cpow_zpow_eq_cpow K p _ ℓ hℓ s,
        show (((m : ℂ) + (n : ℂ)) * s) = (m : ℂ) * s + (n : ℂ) * s by ring, Complex.cpow_add _ _ hN0]
      linear_combination (Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) * hId s

  · intro v hbv hvSQ hKv hψinv W hW g
    have hvS : v ∈ S := (hSbad v).mp hbv
    obtain ⟨gInf, σ, hσ, ⟨t, e, hte, he⟩, hnv⟩ := harchOf 1 (Or.inl rfl)
    obtain ⟨R₁, R₂, m, hR₁, hR₂, hFE⟩ :=
      LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel
        K _hdeg ψ hψ μ hμ hlevS hoff D U gen S hSbad X hXS hXc hXg hXdg hXw hXdw c hc hX0 hBad E hE ν_mul
        v hvS (fun w hw _ => h1S w hw) hadmS hcentS hS hS' 1 ⟨0, LanglandsTunnell.TateLocal.hasConductorExponentAt_one_zero ℚ v⟩
        ⟨gInf, σ, hσ, ⟨t, e, hte, by rw [MonoidHom.one_apply, Units.val_one]; exact he⟩, hnv⟩
    have hB := hlamT v hvS hvSQ R₁ R₂ m hR₁ hR₂ hFE
    rw [← hlamM_tame v hvS hvSQ] at hB
    have h31 := LanglandsTunnell.CubicInduction.localZeta31_fe_one_of_forall_exists_mul_eval_eq_of_eval_mul_eq v
      (X.whittakerLoc v) (inducedEulerPoly ℚ (inducedCoeff K μ) v) (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v)
      (lamM v * ((∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
        ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w)))
      (inducedLevelAt K μ v) (IDM.inducedEulerPoly_ne_zero K _ v) (IDM.inducedEulerPoly_ne_zero K _ v)
      R₁ R₂ m ⟨hR₁, hR₂, hFE⟩ hB
    exact LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
      v (X.whittakerLoc v) _ _ _ _ h31 W hW g

end S_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces (solution)
