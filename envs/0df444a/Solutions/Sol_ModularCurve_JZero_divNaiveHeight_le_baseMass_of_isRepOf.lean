-- Prove2me | solution 1 for ModularCurve.JZero.divNaiveHeight_le_baseMass_of_isRepOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8411791e-b6d4-5991-81ba-77ed8fe42ff5

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Mathlib.Algebra.Ring.Action.Submonoid
import Theorems.Thm_ModularCurve_symVec_mem_of_stable
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_absLogHeight_coeff_le_sum_roots
import Theorems.Thm_ModularCurve_JZero_exists_absLogHeight_jCoord_le_pointHt
import Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_mul_baseHt
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_divNaiveHeight_le_baseMass_of_isRepOf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MHm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (Set.range_subset_iff.mpr h)
  haveI := finiteDimensional_adjoin_range x
  have h3 := Height.inv_finrank_mul_logHeight_inclusion (L := E') hle
    (fun i => (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range x)))
  have htup : (fun i => IntermediateField.inclusion hle
      (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range x))) = fun i => (⟨x i, h i⟩ : E') := by
    funext i; rfl
  unfold absLogHeight
  rw [← htup]
  exact h3.symm

theorem absLogHeight_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (x : ι → AlgebraicClosure ℚ)
    (e : κ ≃ ι) : absLogHeight (x ∘ e) = absLogHeight x := by
  set E' := IntermediateField.adjoin ℚ (Set.range x) with hE'
  haveI : FiniteDimensional ℚ E' := finiteDimensional_adjoin_range x
  have hx : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩
  have hxe : ∀ k, (x ∘ e) k ∈ E' := fun k => hx (e k)
  rw [absLogHeight_eq_of_mem (x ∘ e) E' hxe, absLogHeight_eq_of_mem x E' hx]
  congr 1
  exact Height.logHeight_comp_equiv e (fun i => (⟨x i, hx i⟩ : E'))

theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem pointHt_nonneg {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v :=
  absLogHeight_nonneg _

variable (N : ℕ) [NeZero N]

abbrev jbar : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

theorem ne_cuspInftyBar_of_ord_nonneg {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : 0 ≤ v.ord (jbar N)) : v ≠ cuspInftyBar N := by
  rintro rfl
  have h := ModularCurve.ord_cuspInftyBar_coeffEmb_jq N
  change (cuspInftyBar N).ord (jbar N) = -1 at h
  omega

theorem symPoly_eq_prod_filter (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    symPoly N D = ∏ v ∈ D.support.filter (fun v => 0 ≤ v.ord (jbar N)),
      (Polynomial.X - Polynomial.C (jCoord N v)) ^ (D v).toNat := by
  unfold ModularCurve.symPoly
  rw [Finsupp.prod, ← Finset.prod_filter_mul_prod_filter_not D.support (fun v => 0 ≤ v.ord (jbar N))]
  have h2 : ∏ v ∈ D.support.filter (fun v => ¬ 0 ≤ v.ord (jbar N)), jFactor N v ^ (D v).toNat = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [ModularCurve.jFactor_of_neg (not_le.mp hv.2), one_pow]
  rw [h2, mul_one]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Finset.mem_filter] at hv
  rw [ModularCurve.jFactor_of_nonneg hv.2]

theorem sum_toNat_eq_of_rep (g' : ℕ)
    (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (heff : ∀ v, 0 ≤ D v)
    (hE : (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) :
    ∑ v ∈ D.support, (D v).toNat = g' := by
  classical
  have hker : Divisor.degree (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = 0 := E.2
  have hdegD : Divisor.degree D = (g' : ℤ) := by
    rw [← hE, map_add, map_zsmul, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), hker]
    simp
  have hdeg_sum : Divisor.degree D = ∑ v ∈ D.support, D v := by
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun v _ => by
      rw [AddMonoidHom.mulRight_apply, ModularCurve.deg_eq_one_modularFunctionFieldBar N v]
      simp
  have h4 : (∑ v ∈ D.support, ((D v).toNat : ℤ)) = (g' : ℤ) := by
    rw [← hdegD, hdeg_sum]
    exact Finset.sum_congr rfl fun v _ => Int.toNat_of_nonneg (heff v)
  exact_mod_cast h4

theorem baseMass_eq_sum {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    JZero.baseMass N s D = ∑ v ∈ D.support, (D v : ℝ) * baseHt s (cuspInftyBar N) v := by
  classical
  unfold JZero.baseMass
  rw [Finsupp.sum, Finsupp.support_erase]
  have h : ∑ v ∈ D.support, (D v : ℝ) * baseHt s (cuspInftyBar N) v
      = ∑ v ∈ D.support.erase (cuspInftyBar N), (D v : ℝ) * baseHt s (cuspInftyBar N) v :=
    (Finset.sum_erase _ (by simp [baseHt])).symm
  rw [h]
  exact Finset.sum_congr rfl fun v hv => by
    rw [Finset.mem_erase] at hv
    rw [Finsupp.erase_ne hv.1]

theorem divNaiveHeight_eq (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (h : ∀ k, symVec N g' D k ∈ K) :
    divNaiveHeight N K g' D = (Module.finrank ℚ K : ℝ) * absLogHeight (symVec N g' D) := by
  unfold ModularCurve.divNaiveHeight
  rw [dif_pos h, absLogHeight_eq_of_mem (symVec N g' D) K h, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), one_mul]

theorem symVec_eq_comp_rev (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    symVec N g' D = (fun k : Fin (g' + 1) => (symPoly N D).coeff k) ∘ Fin.revPerm := by
  funext k
  simp only [ModularCurve.symVec, Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  congr 1
  omega

end P2MHm

end

set_option synthInstance.maxHeartbeats 1600000 in
open AlgebraicCurve ModularCurve ModularCurve.JZero P2MHm in
theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ κ C : ℝ, 0 ≤ κ ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        divNaiveHeight N K g' D ≤ κ * baseMass N s D + C := by
  obtain ⟨B', C', hB'0, hB⟩ := ModularCurve.JZero.exists_absLogHeight_jCoord_le_pointHt N s hs
  obtain ⟨C'', hC⟩ := ModularCurve.JZero.exists_pointHt_le_mul_baseHt N s hs
  set dK : ℝ := (Module.finrank ℚ K : ℝ) with hdK
  set m : ℝ := (embDegree N : ℝ) with hm
  have hdK0 : 0 ≤ dK := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  refine ⟨dK * (B' * m), dK * ((B' * |C''| + |C'|) * g' + g' * Real.log 2), by positivity, ?_⟩
  rintro c D ⟨E, heff, hE, hstab, -⟩

  have hmem : ∀ k, symVec N g' D k ∈ K := fun k => ModularCurve.symVec_mem_of_stable N K g' D hstab k
  rw [divNaiveHeight_eq N K g' D hmem]

  set t := D.support.filter (fun v => 0 ≤ v.ord (jbar N)) with ht
  have hsumall : ∑ v ∈ D.support, (D v).toNat = g' := sum_toNat_eq_of_rep N g' E D heff hE
  have hsub_t : t ⊆ D.support := Finset.filter_subset _ _
  have hsum_t : ∑ v ∈ t, (D v).toNat ≤ g' := hsumall ▸ Finset.sum_le_sum_of_subset hsub_t
  have hA := AlgebraicCurve.absLogHeight_coeff_le_sum_roots t (jCoord N) (fun v => (D v).toNat) hsum_t
  have hsym : absLogHeight (symVec N g' D)
      = absLogHeight (fun k : Fin (g' + 1) => (∏ v ∈ t, (Polynomial.X - Polynomial.C (jCoord N v)) ^ (D v).toNat).coeff k) := by
    rw [symVec_eq_comp_rev N g' D, absLogHeight_comp_equiv, symPoly_eq_prod_filter N D]

  have hpt : ∀ v ∈ t, absLogHeight ![jCoord N v, 1] ≤ B' * (m * baseHt s (cuspInftyBar N) v + |C''|) + C' := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h1 := hB v hv.2
    have h2 := hC v (ne_cuspInftyBar_of_ord_nonneg N hv.2)
    have h3 := le_abs_self C''
    nlinarith
  have hnn : ∀ v ∈ D.support, 0 ≤ m * baseHt s (cuspInftyBar N) v + |C''| := by
    intro v _
    by_cases hv : v = cuspInftyBar N
    · rw [hv]; simp [baseHt]
    · have h2 := hC v hv
      linarith [pointHt_nonneg s v, le_abs_self C'']
  have ht_sub : t ⊆ D.support := Finset.filter_subset _ _
  have hcoef : ∀ v, (((D v).toNat : ℕ) : ℝ) = (D v : ℝ) := fun v => by
    have := Int.toNat_of_nonneg (heff v)
    exact_mod_cast this
  have hDnn : ∀ v, (0 : ℝ) ≤ (D v : ℝ) := fun v => by exact_mod_cast heff v
  have hsum_t_real : ∑ v ∈ t, (D v : ℝ) ≤ g' := by
    have : ((∑ v ∈ t, (D v).toNat : ℕ) : ℝ) ≤ (g' : ℝ) := by exact_mod_cast hsum_t
    rw [Nat.cast_sum] at this
    simpa only [hcoef] using this
  have hsum_e_real : ∑ v ∈ D.support, (D v : ℝ) ≤ g' := by
    have : ((∑ v ∈ D.support, (D v).toNat : ℕ) : ℝ) = (g' : ℝ) := by exact_mod_cast hsumall
    rw [Nat.cast_sum] at this
    simp only [hcoef] at this
    exact this.le

  have step1 : ∑ v ∈ t, (((D v).toNat : ℕ) : ℝ) * absLogHeight ![jCoord N v, 1]
      ≤ B' * ∑ v ∈ t, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|) + |C'| * g' := by
    calc ∑ v ∈ t, (((D v).toNat : ℕ) : ℝ) * absLogHeight ![jCoord N v, 1]
        ≤ ∑ v ∈ t, (D v : ℝ) * (B' * (m * baseHt s (cuspInftyBar N) v + |C''|) + |C'|) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hcoef]
          refine mul_le_mul_of_nonneg_left ?_ (hDnn v)
          linarith [hpt v hv, le_abs_self C']
      _ = B' * ∑ v ∈ t, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|) + |C'| * ∑ v ∈ t, (D v : ℝ) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun v _ => by ring
      _ ≤ B' * ∑ v ∈ t, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|) + |C'| * g' := by
          have := mul_le_mul_of_nonneg_left hsum_t_real (abs_nonneg C')
          linarith
  have step2 : ∑ v ∈ t, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|)
      ≤ ∑ v ∈ D.support, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|) :=
    Finset.sum_le_sum_of_subset_of_nonneg ht_sub fun v hv _ => mul_nonneg (hDnn v) (hnn v hv)
  have step3 : ∑ v ∈ D.support, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|)
      ≤ m * baseMass N s D + |C''| * g' := by
    rw [baseMass_eq_sum N s D, Finset.mul_sum]
    have : ∑ v ∈ D.support, (D v : ℝ) * (m * baseHt s (cuspInftyBar N) v + |C''|)
        = ∑ v ∈ D.support, m * ((D v : ℝ) * baseHt s (cuspInftyBar N) v)
          + |C''| * ∑ v ∈ D.support, (D v : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [this]
    have h1 : |C''| * ∑ v ∈ D.support, (D v : ℝ) ≤ |C''| * g' :=
      mul_le_mul_of_nonneg_left hsum_e_real (abs_nonneg _)
    linarith
  have habs : absLogHeight (symVec N g' D) ≤ B' * m * baseMass N s D + ((B' * |C''| + |C'|) * g' + g' * Real.log 2) := by
    rw [hsym]
    have h23 := mul_le_mul_of_nonneg_left (step2.trans step3) hB'0
    nlinarith [hA, step1, h23]
  have := mul_le_mul_of_nonneg_left habs hdK0
  nlinarith [this]

end S_ModularCurve_JZero_divNaiveHeight_le_baseMass_of_isRepOf
end P2MW
export P2MW.S_ModularCurve_JZero_divNaiveHeight_le_baseMass_of_isRepOf (solution)
