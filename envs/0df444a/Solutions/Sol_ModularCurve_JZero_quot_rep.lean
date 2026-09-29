-- Prove2me | solution 1 for ModularCurve.JZero.quot_rep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ac579134-93ce-5dc4-9fc0-a21f98ae2bc4

import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_quot_rep
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.jqNModC_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option Elab.async false
set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_quot_rep.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree deg_eq_one_modularFunctionFieldBar"
p2m_open "ModularCurve"

def CoreQuot.negPart {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Divisor K F) : Divisor K F :=
  Finsupp.mapRange (fun m : ℤ => max (-m) 0) (by simp) A

theorem CoreQuot.negPart_apply {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Divisor K F)
    (w : Place K F) : CoreQuot.negPart A w = max (-A w) 0 := by
  simp [CoreQuot.negPart]

theorem CoreQuot.negPart_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Divisor K F)
    (w : Place K F) : 0 ≤ CoreQuot.negPart A w := by
  rw [CoreQuot.negPart_apply]; exact le_max_right _ _

theorem CoreQuot.neg_le_negPart {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Divisor K F)
    (w : Place K F) : -A w ≤ CoreQuot.negPart A w := by
  rw [CoreQuot.negPart_apply]; exact le_max_left _ _

theorem CoreQuot.sum_negPart_le_mass {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Divisor K F) :
    ((CoreQuot.negPart A).sum fun _ m => (m : ℝ)) ≤ A.sum fun _ m => |(m : ℝ)| := by
  have h1 : ((CoreQuot.negPart A).sum fun _ m => (m : ℝ)) = A.sum fun _ m => ((max (-m) 0 : ℤ) : ℝ) := by
    unfold CoreQuot.negPart
    exact Finsupp.sum_mapRange_index (fun _ => by simp)
  rw [h1]
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun w _ => ?_
  push_cast
  exact max_le (neg_le_abs _) (abs_nonneg _)

theorem CoreQuot.degree_eq_sum (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun w _ => ?_
  simp [deg_eq_one_modularFunctionFieldBar N w]

theorem CoreQuot.embDivisor_apply_of_ne (N : ℕ) [NeZero N]
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hw : w ≠ cuspInftyBar N) : embDivisor N w = 0 := by
  simp [embDivisor, Ne.symm hw]

theorem CoreQuot.degree_embDivisor (N : ℕ) [NeZero N] :
    Divisor.degree (embDivisor N) = (embDegree N : ℤ) := by
  unfold embDivisor
  rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N),
    smul_eq_mul]
  simp

theorem CoreQuot.one_le_embDegree (N : ℕ) [NeZero N] : (1 : ℤ) ≤ (embDegree N : ℤ) := by
  have : 1 ≤ embDegree N := by unfold embDegree; omega
  exact_mod_cast this

private theorem CoreQuot.quot_rep_main (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C₀ : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      f ≠ 0 → (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), A v = 0 → v ≠ cuspInftyBar N →
      ∃ (k : ℕ) (u₁ u₂ : modularFunctionFieldBar N),
        (k : ℝ) ≤ (A.sum fun _ m => |(m : ℝ)|) + C₀ ∧
        u₁ ∈ riemannRochSpace ((k : ℤ) • embDivisor N) ∧
        u₂ ∈ riemannRochSpace ((k : ℤ) • embDivisor N) ∧
        u₂ ≠ 0 ∧ v.ord u₂ = 0 ∧ f * u₂ = u₁ := by
  classical
  have _ := hs
  obtain ⟨g₀, hdrop⟩ := exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree N
  refine ⟨(g₀ : ℝ), ?_⟩
  intro f A hf hA v hAv hvo

  have hAnv : CoreQuot.negPart A v = 0 := by rw [CoreQuot.negPart_apply, hAv]; simp
  have hdegAn : Divisor.degree (CoreQuot.negPart A) = (CoreQuot.negPart A).sum fun _ n => n :=
    CoreQuot.degree_eq_sum N (CoreQuot.negPart A)
  have hdegAn0 : 0 ≤ Divisor.degree (CoreQuot.negPart A) := by
    rw [hdegAn]
    unfold Finsupp.sum
    exact Finset.sum_nonneg fun w _ => CoreQuot.negPart_nonneg A w

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = Divisor.degree (CoreQuot.negPart A) :=
    ⟨(Divisor.degree (CoreQuot.negPart A)).toNat, Int.toNat_of_nonneg hdegAn0⟩
  set k : ℕ := n + g₀ with hk
  set D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (k : ℤ) • embDivisor N - CoreQuot.negPart A with hD₁
  have hD₁w : ∀ w, D₁ w = (k : ℤ) * embDivisor N w - CoreQuot.negPart A w := fun w => by
    simp [hD₁, Finsupp.sub_apply, Finsupp.smul_apply]
  have hD₁v : D₁ v = 0 := by
    rw [hD₁w, CoreQuot.embDivisor_apply_of_ne N hvo, hAnv]; simp
  have hdegD₁ : (g₀ : ℤ) ≤ Divisor.degree D₁ := by
    have h1 : Divisor.degree D₁
        = (k : ℤ) * (embDegree N : ℤ) - Divisor.degree (CoreQuot.negPart A) := by
      rw [hD₁, map_sub, map_zsmul, CoreQuot.degree_embDivisor N, smul_eq_mul]
    have h2 : (1 : ℤ) ≤ (embDegree N : ℤ) := CoreQuot.one_le_embDegree N
    have h3 : (k : ℤ) = n + g₀ := by simp [hk]
    have h4 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    rw [h1]
    nlinarith [h2, h3, h4, hn]

  obtain ⟨u₂, hu₂D, hu₂not⟩ := hdrop D₁ hdegD₁ v
  have hu₂ne : u₂ ≠ 0 := by
    rintro rfl
    exact hu₂not (Submodule.zero_mem _)
  rw [mem_riemannRochSpace_iff] at hu₂D
  have hord : ∀ w, -D₁ w ≤ w.ord u₂ := fun w => (hu₂D w).resolve_left hu₂ne
  have hordv : v.ord u₂ = 0 := by
    have hge : 0 ≤ v.ord u₂ := by simpa [hD₁v] using hord v
    have hlt : v.ord u₂ < 1 := by
      by_contra hcon
      have hcon' : 1 ≤ v.ord u₂ := not_lt.mp hcon
      apply hu₂not
      rw [mem_riemannRochSpace_iff]
      intro w
      right
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      by_cases hw : v = w
      · subst hw
        rw [if_pos rfl, hD₁v]
        simpa using hcon'
      · rw [if_neg hw, sub_zero]
        exact hord w
    omega
  refine ⟨k, f * u₂, u₂, ?_, ?_, ?_, hu₂ne, hordv, rfl⟩
  ·
    have h1 : ((n : ℤ) : ℝ) = ((Divisor.degree (CoreQuot.negPart A) : ℤ) : ℝ) := by rw [hn]
    have h2 : ((Divisor.degree (CoreQuot.negPart A) : ℤ) : ℝ)
        = (CoreQuot.negPart A).sum fun _ m => (m : ℝ) := by
      rw [hdegAn]
      push_cast [Finsupp.sum]
      try rfl
    have h3 := CoreQuot.sum_negPart_le_mass A
    have h4 : (k : ℝ) = (n : ℝ) + g₀ := by simp [hk]
    have h5 : (n : ℝ) = ((n : ℤ) : ℝ) := by simp
    linarith
  ·
    rw [mem_riemannRochSpace_iff]
    intro w
    right
    rw [Place.ord_mul w hf hu₂ne, ← hA w, Finsupp.smul_apply, smul_eq_mul]
    have h1 := hord w
    have h2 := hD₁w w
    have h3 := CoreQuot.neg_le_negPart A w
    linarith
  ·
    rw [mem_riemannRochSpace_iff]
    intro w
    right
    rw [Finsupp.smul_apply, smul_eq_mul]
    have h1 := hord w
    have h2 := hD₁w w
    have h3 := CoreQuot.negPart_nonneg A w
    linarith

end ModularCurve

end

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_JZero_quot_rep.ModularCurve in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C₀ : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      f ≠ 0 → (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), A v = 0 → v ≠ cuspInftyBar N →
      ∃ (k : ℕ) (u₁ u₂ : modularFunctionFieldBar N),
        (k : ℝ) ≤ (A.sum fun _ m => |(m : ℝ)|) + C₀ ∧
        u₁ ∈ riemannRochSpace ((k : ℤ) • embDivisor N) ∧
        u₂ ∈ riemannRochSpace ((k : ℤ) • embDivisor N) ∧
        u₂ ≠ 0 ∧ v.ord u₂ = 0 ∧ f * u₂ = u₁ := by
  exact ModularCurve.CoreQuot.quot_rep_main N s hs

end S_ModularCurve_JZero_quot_rep
end P2MW
export P2MW.S_ModularCurve_JZero_quot_rep (solution)
