-- Prove2me | solution 1 for ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1453c65c-23ad-58e2-bf00-84f47d819305

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_Height_mulHeightBound_map_le
import Theorems.Thm_ModularCurve_JZero_exists_isHomogeneous_sum_aeval_mul_eq_pow
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace P2MBpfH

open AlgebraicCurve Height NumberField MvPolynomial

noncomputable section

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

section Descend

variable {σ : Type*} (E : IntermediateField ℚ (AlgebraicClosure ℚ))

def descend (f : MvPolynomial σ (AlgebraicClosure ℚ)) (hf : ∀ s, coeff s f ∈ E) : MvPolynomial σ E :=
  ∑ s ∈ f.support, monomial s (⟨coeff s f, hf s⟩ : E)

theorem map_descend (f : MvPolynomial σ (AlgebraicClosure ℚ)) (hf : ∀ s, coeff s f ∈ E) :
    map (algebraMap E (AlgebraicClosure ℚ)) (descend E f hf) = f := by
  unfold descend
  rw [map_sum]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_monomial]
  rfl

theorem coeff_descend (f : MvPolynomial σ (AlgebraicClosure ℚ)) (hf : ∀ s, coeff s f ∈ E) (s : σ →₀ ℕ) :
    ((coeff s (descend E f hf) : E) : AlgebraicClosure ℚ) = coeff s f := by
  conv_rhs => rw [← map_descend E f hf]
  rw [coeff_map]
  rfl

theorem isHomogeneous_descend (f : MvPolynomial σ (AlgebraicClosure ℚ)) (hf : ∀ s, coeff s f ∈ E) {n : ℕ}
    (h : f.IsHomogeneous n) : (descend E f hf).IsHomogeneous n := by
  intro d hd
  apply h
  intro h0
  apply hd
  apply Subtype.ext
  rw [coeff_descend]
  exact h0

end Descend

private theorem _root_.P2MBpfH.mulHeightBound_nonneg {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι ι' : Type*}
    (p : ι' → MvPolynomial ι K) : 0 ≤ Height.mulHeightBound p := by
  rw [Height.mulHeightBound_eq]
  refine mul_nonneg (Multiset.prod_nonneg fun a ha => ?_) (finprod_nonneg fun v => ?_)
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    exact Real.iSup_nonneg fun j => by
      rw [MvPolynomial.sum_def]
      exact Finset.sum_nonneg fun s _ => apply_nonneg v _
  · exact Real.iSup_nonneg fun j => le_trans zero_le_one (le_max_right _ _)

p2m_export "P2MBpfH" "mulHeightBound_nonneg"

theorem absLogHeight_le_of_certificate {a b Mdeg : ℕ} (hb : 0 < b)
    (q : Fin a → Fin b → MvPolynomial (Fin a) (AlgebraicClosure ℚ)) (hq : ∀ k j, (q k j).IsHomogeneous Mdeg)
    (Mmat : Fin b → Fin a → AlgebraicClosure ℚ) :
    ∃ C : ℝ, ∀ (x : Fin a → AlgebraicClosure ℚ) (y : Fin b → AlgebraicClosure ℚ) (c : AlgebraicClosure ℚ),
      c ≠ 0 → (∀ j, y j = c * ∑ i, Mmat j i * x i) →
      (∀ k, ∑ j, MvPolynomial.eval x (q k j) * (∑ i, Mmat j i * x i) = x k ^ (Mdeg + 1)) →
      AlgebraicCurve.absLogHeight x ≤ AlgebraicCurve.absLogHeight y + C := by
  classical

  let I₀ := (Σ (k : Fin a) (j : Fin b), ↥(q k j).support) ⊕ (Fin b × Fin a)
  let gen₀ : I₀ → AlgebraicClosure ℚ :=
    Sum.elim (fun t => coeff (↑t.2.2) (q t.1 t.2.1)) (fun ji => Mmat ji.1 ji.2)
  let E₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ (Set.range gen₀)
  haveI hE₀fd : FiniteDimensional ℚ E₀ := finiteDimensional_adjoin_range gen₀
  have hcoeff₀ : ∀ k j s, coeff s (q k j) ∈ E₀ := by
    intro k j s
    by_cases hs : s ∈ (q k j).support
    · exact IntermediateField.subset_adjoin ℚ _ ⟨Sum.inl ⟨k, j, ⟨s, hs⟩⟩, rfl⟩
    · rw [MvPolynomial.notMem_support_iff.mp hs]; exact zero_mem _
  have hM₀ : ∀ j i, Mmat j i ∈ E₀ := fun j i => IntermediateField.subset_adjoin ℚ _ ⟨Sum.inr (j, i), rfl⟩
  let q₀ : Fin a × Fin b → MvPolynomial (Fin a) E₀ := fun kj => descend E₀ (q kj.1 kj.2) (hcoeff₀ kj.1 kj.2)
  have hq₀ : ∀ kj, (q₀ kj).IsHomogeneous Mdeg := fun kj => isHomogeneous_descend E₀ _ _ (hq kj.1 kj.2)
  let B₀ : ℝ := Height.mulHeightBound q₀
  have hB₀ : 0 ≤ B₀ := mulHeightBound_nonneg q₀
  let d₀ : ℝ := Module.finrank ℚ E₀
  have hd₀ : 0 < d₀ := by
    have h0 : 0 < Module.finrank ℚ E₀ := Module.finrank_pos
    have : (0 : ℝ) < (Module.finrank ℚ E₀ : ℝ) := by exact_mod_cast h0
    exact this
  refine ⟨Real.log b + Real.log (max B₀ 1) / d₀, fun x y c hc hy hcert => ?_⟩

  let I' := I₀ ⊕ (Fin a ⊕ (Fin b ⊕ Unit))
  let gen' : I' → AlgebraicClosure ℚ := Sum.elim gen₀ (Sum.elim x (Sum.elim y (fun _ => c)))
  let E' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ (Set.range gen')
  haveI hE'fd : FiniteDimensional ℚ E' := finiteDimensional_adjoin_range gen'
  have hle : E₀ ≤ E' := IntermediateField.adjoin.mono ℚ _ _ (by
    rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ ⟨Sum.inr (Sum.inl i), rfl⟩
  have hyE : ∀ j, y j ∈ E' := fun j => IntermediateField.subset_adjoin ℚ _ ⟨Sum.inr (Sum.inr (Sum.inl j)), rfl⟩
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ ⟨Sum.inr (Sum.inr (Sum.inr ())), rfl⟩
  letI : Algebra E₀ E' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have halg : ∀ z : E₀, ((algebraMap E₀ E' z : E') : AlgebraicClosure ℚ) = (z : AlgebraicClosure ℚ) := fun z => rfl
  haveI : IsScalarTower ℚ E₀ E' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : Module.Finite E₀ E' := Module.Finite.of_restrictScalars_finite ℚ E₀ E'

  let x' : Fin a → E' := fun i => ⟨x i, hxE i⟩
  let y' : Fin b → E' := fun j => ⟨y j, hyE j⟩
  let c' : E' := ⟨c, hcE⟩
  have hc' : c' ≠ 0 := fun h => hc (congrArg Subtype.val h)
  let M' : Fin b → Fin a → E' := fun j i => ⟨Mmat j i, hle (hM₀ j i)⟩
  let q' : Fin a × Fin b → MvPolynomial (Fin a) E' := fun kj => map (algebraMap E₀ E') (q₀ kj)
  let p' : Fin b → MvPolynomial (Fin a) E' := fun j => ∑ i, MvPolynomial.C (M' j i) * MvPolynomial.X i
  have hq' : ∀ kj, (q' kj).IsHomogeneous Mdeg := fun kj => (hq₀ kj).map _
  have hp'eval : ∀ j, eval x' (p' j) = ∑ i, M' j i * x' i := by
    intro j
    show eval x' (∑ i, MvPolynomial.C (M' j i) * MvPolynomial.X i) = _
    simp only [map_sum, map_mul, eval_C, eval_X]
  have hq'eval : ∀ kj, (E'.val : E' →+* AlgebraicClosure ℚ) (eval x' (q' kj)) = eval x (q kj.1 kj.2) := by
    intro kj
    have h1 := MvPolynomial.eval₂_comp_left (E'.val : E' →+* AlgebraicClosure ℚ) (algebraMap E₀ E') x' (q₀ kj)
    have h2 : (E'.val : E' →+* AlgebraicClosure ℚ).comp (algebraMap E₀ E') = algebraMap E₀ (AlgebraicClosure ℚ) := by
      ext z; exact halg z
    have h3 : (⇑(E'.val : E' →+* AlgebraicClosure ℚ) ∘ x') = x := by funext i; rfl
    have h4 : map (algebraMap E₀ (AlgebraicClosure ℚ)) (q₀ kj) = q kj.1 kj.2 := map_descend E₀ _ _
    rw [h2, h3, ← eval_map, ← eval_map, h4] at h1
    exact h1
  have hcert' : ∀ k, ∑ j, eval x' (q' (k, j)) * eval x' (p' j) = x' k ^ (Mdeg + 1) := by
    intro k
    apply Subtype.ext
    show (E'.val : E' →+* AlgebraicClosure ℚ) (∑ j, eval x' (q' (k, j)) * eval x' (p' j))
      = (E'.val : E' →+* AlgebraicClosure ℚ) (x' k ^ (Mdeg + 1))
    rw [map_sum, map_pow]
    have hxk : (E'.val : E' →+* AlgebraicClosure ℚ) (x' k) = x k := rfl
    rw [hxk, ← hcert k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hq'eval (k, j), hp'eval, map_sum]
    congr 1

  have hge := Height.logHeight_eval_ge (K := E') (M := Mdeg) (N := 1) (q := q') hq' p' hcert'
  have hp'y : (fun j => eval x' (p' j)) = c'⁻¹ • y' := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, hp'eval]
    have : y' j = c' * ∑ i, M' j i * x' i := by
      apply Subtype.ext
      show y j = (E'.val : E' →+* AlgebraicClosure ℚ) (c' * ∑ i, M' j i * x' i)
      rw [map_mul, map_sum, hy j]
      congr 1
    rw [this, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [hp'y, Height.logHeight_smul_eq_logHeight _ (inv_ne_zero hc')] at hge

  have htw : (totalWeight E' : ℝ) = Module.finrank ℚ E' := by exact_mod_cast totalWeight_eq_finrank E'
  have hcard : (Nat.card (Fin b) : ℝ) = b := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  set B' : ℝ := Height.mulHeightBound q' with hB'def
  set d' : ℝ := (Module.finrank ℚ E' : ℝ) with hd'def
  set m : ℕ := Module.finrank E₀ E' with hmdef
  have hm1 : 1 ≤ m := Module.finrank_pos
  have hdd : d' = d₀ * m := by
    rw [hd'def, hmdef, ← Module.finrank_mul_finrank ℚ E₀ E']; push_cast; ring
  have hd' : 0 < d' := by rw [hdd]; exact mul_pos hd₀ (by exact_mod_cast hm1)
  have hB'le : B' ≤ B₀ ^ m := Height.mulHeightBound_map_le (K := E₀) (L := E') q₀
  have hmaxle : max B' 1 ≤ (max B₀ 1) ^ m :=
    max_le (hB'le.trans (pow_le_pow_left₀ hB₀ (le_max_left _ _) m)) (one_le_pow₀ (le_max_right _ _))
  have hmaxpos : 0 < max B' 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlogmax : Real.log (max B' 1) ≤ m * Real.log (max B₀ 1) := by
    rw [← Real.log_pow]; exact Real.log_le_log hmaxpos hmaxle
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpow : 0 < (b : ℝ) ^ totalWeight E' := pow_pos (by linarith) _

  rw [hcard, Real.log_mul hbpow.ne' hmaxpos.ne', Real.log_pow, htw] at hge
  simp only [Nat.cast_one, one_mul] at hge

  rw [absLogHeight_eq_of_mem x E' hxE, absLogHeight_eq_of_mem y E' hyE]
  change d'⁻¹ * logHeight x' ≤ d'⁻¹ * logHeight y' + (Real.log b + Real.log (max B₀ 1) / d₀)

  have key : logHeight x' ≤ logHeight y' + d' * Real.log b + d' * (Real.log (max B₀ 1) / d₀) := by
    have : d' * (Real.log (max B₀ 1) / d₀) = m * Real.log (max B₀ 1) := by
      rw [hdd]; field_simp
    rw [this]
    linarith
  have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hd'.le)
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hd'.ne', one_mul, one_mul] at this
  linarith

end

end P2MBpfH

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve

noncomputable section
namespace P2MBpf

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem exists_forall_ord_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem evalVec_apply (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]
  simp only [dif_pos hr]

theorem evalVec_pivot (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v (pivotIndex s v hr) = 1 := by
  rw [evalVec_apply hr, mul_inv_cancel₀ (hs _), Place.evalAt_one]

theorem evalVec_ne_zero (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v ≠ 0 := by
  intro h
  have := congrFun h (pivotIndex s v hr)
  rw [evalVec_pivot hr s hs v] at this
  exact one_ne_zero this

theorem ratio_pivot_mem (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    s i * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs i) (inv_ne_zero (hs _)))
    (by rw [v.ord_mul (hs i) (inv_ne_zero (hs _)), v.ord_inv]; linarith [ord_pivot_le hr s v i])

end Pivot

section AbsHeight

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

theorem absLogHeight_smul {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : absLogHeight (c • x) = absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (insert c (Set.range x)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert c _)
  have hx' : ∀ i, x i ∈ E' := fun i =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem c ⟨i, rfl⟩)
  have hcx : ∀ i, (c • x) i ∈ E' := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]; exact mul_mem hcE (hx' i)
  rw [absLogHeight_eq_of_mem (c • x) E' hcx, absLogHeight_eq_of_mem x E' hx']
  congr 1
  convert Height.logHeight_smul_eq_logHeight (fun i => (⟨x i, hx' i⟩ : E')) (c := ⟨c, hcE⟩) ?_ using 2
  all_goals first
    | exact fun h0 => hc (by simpa using congrArg Subtype.val h0)
    | (funext i; apply Subtype.ext; simp [Pi.smul_apply, smul_eq_mul])

theorem absLogHeight_mul_eq_add {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (x : ι → AlgebraicClosure ℚ) (y : κ → AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (e : μ ≃ ι × κ) :
    absLogHeight (fun m => x (e m).1 * y (e m).2) = absLogHeight x + absLogHeight y := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range y) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hyE : ∀ j, y j ∈ E' := fun j => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)
  have hpE : ∀ m, x (e m).1 * y (e m).2 ∈ E' := fun m => mul_mem (hxE _) (hyE _)
  rw [absLogHeight_eq_of_mem _ E' hpE, absLogHeight_eq_of_mem x E' hxE, absLogHeight_eq_of_mem y E' hyE,
    ← mul_add]
  congr 1
  have hx' : (fun i => (⟨x i, hxE i⟩ : E')) ≠ 0 := by
    intro h; apply hx; funext i; simpa using congrArg Subtype.val (congrFun h i)
  have hy' : (fun j => (⟨y j, hyE j⟩ : E')) ≠ 0 := by
    intro h; apply hy; funext j; simpa using congrArg Subtype.val (congrFun h j)
  have hfun : (fun m => (⟨x (e m).1 * y (e m).2, hpE m⟩ : E'))
      = (fun q : ι × κ => (⟨x q.1, hxE q.1⟩ : E') * (⟨y q.2, hyE q.2⟩ : E')) ∘ e := by
    funext m
    apply Subtype.ext
    rfl
  rw [hfun, Height.logHeight_comp_equiv e, Height.logHeight_fun_mul_eq hx' hy']

end AbsHeight

section Eval

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem evalAt_add_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem smul_mem_of_mem (v : Place (AlgebraicClosure ℚ) F) (a : AlgebraicClosure ℚ) {f : F}
    (hf : f ∈ v.toValuationSubring) : a • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    (a : AlgebraicClosure ℚ) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

theorem sum_smul_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (c : ι → AlgebraicClosure ℚ) {f : ι → F} (hf : ∀ i, f i ∈ v.toValuationSubring) :
    (∑ i ∈ S, c i • f i) ∈ v.toValuationSubring :=
  sum_mem fun i _ => smul_mem_of_mem v (c i) (hf i)

theorem evalAt_sum_smul_of_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (hv : v.IsRational) (c : ι → AlgebraicClosure ℚ) {f : ι → F}
    (hf : ∀ i, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (v.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem v hv (smul_mem_of_mem v _ (hf a)) (sum_smul_mem S v c hf),
      evalAt_smul_of_mem v hv _ (hf a), ih]

end Eval

section Linear

theorem absLogHeight_linear_le {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι]
    (M : κ → ι → AlgebraicClosure ℚ) (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (fun j => ∑ i, M j i * x i)
      ≤ Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2) + absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range (fun q : κ × ι => M q.1 q.2)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hME : ∀ q : κ × ι, M q.1 q.2 ∈ E' := fun q => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨q, rfl⟩)
  have hyE : ∀ j, (∑ i, M j i * x i) ∈ E' := fun j => sum_mem fun i _ => mul_mem (hME (j, i)) (hxE i)
  rw [absLogHeight_eq_of_mem _ E' hyE, absLogHeight_eq_of_mem _ E' hME, absLogHeight_eq_of_mem x E' hxE]
  have hd : (0 : ℝ) < Module.finrank ℚ E' := by exact_mod_cast Module.finrank_pos
  have hfun : (fun j => (⟨∑ i, M j i * x i, hyE j⟩ : E'))
      = fun j => ∑ i, (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E') := by
    funext j
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
  have key := Height.logHeight_linearMap_apply_le (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
    (fun i => (⟨x i, hxE i⟩ : E'))
  rw [NumberField.totalWeight_eq_finrank, Nat.card_eq_fintype_card] at key
  rw [hfun]
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  calc (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun j => ∑ i,
          (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E'))
      ≤ (Module.finrank ℚ E' : ℝ)⁻¹ * ((Module.finrank ℚ E' : ℝ) * Real.log (Fintype.card ι)
          + Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + Height.logHeight (fun i => (⟨x i, hxE i⟩ : E'))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hd.le)
    _ = Real.log (Fintype.card ι)
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hxE i⟩ : E')) := by
        field_simp

theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

end Linear

end P2MBpf

end

theorem P2MBpf.mulHeightBound_nonneg {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι ι' : Type*}
    (p : ι' → MvPolynomial ι K) : 0 ≤ Height.mulHeightBound p := by
  rw [Height.mulHeightBound_eq]
  refine mul_nonneg (Multiset.prod_nonneg fun a ha => ?_) (finprod_nonneg fun v => ?_)
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    exact Real.iSup_nonneg fun j => by
      rw [MvPolynomial.sum_def]
      exact Finset.sum_nonneg fun s _ => apply_nonneg v _
  · exact Real.iSup_nonneg fun j => le_trans zero_le_one (le_max_right _ _)

namespace P2MBpf

open AlgebraicCurve ModularCurve MvPolynomial

section Generic

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem evalAt_pow_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (n : ℕ) : v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, v.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih]

theorem evalAt_sum_mul_of_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    {f g : ι → F} (hf : ∀ i, f i ∈ v.toValuationSubring) (hg : ∀ i, g i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ S, f i * g i) = ∑ i ∈ S, v.evalAt (f i) * v.evalAt (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (v.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem v hv (mul_mem (hf a) (hg a)) (sum_mem fun i _ => mul_mem (hf i) (hg i)),
      v.evalAt_mul_of_mem hv (hf a) (hg a), ih]

theorem aeval_mem_of_mem {a : ℕ} (v : Place (AlgebraicClosure ℚ) F) {y : Fin a → F}
    (hy : ∀ i, y i ∈ v.toValuationSubring) (q : MvPolynomial (Fin a) (AlgebraicClosure ℚ)) :
    aeval y q ∈ v.toValuationSubring := by
  induction q using MvPolynomial.induction_on with
  | C c => rw [aeval_C]; exact v.algebraMap_mem' c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (hy i)

theorem evalAt_aeval_of_mem {a : ℕ} (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {y : Fin a → F}
    (hy : ∀ i, y i ∈ v.toValuationSubring) (q : MvPolynomial (Fin a) (AlgebraicClosure ℚ)) :
    v.evalAt (aeval y q) = aeval (fun i => v.evalAt (y i)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => rw [aeval_C, aeval_C, v.evalAt_algebraMap_eq]; rfl
  | add p q hp hq => rw [map_add, map_add, evalAt_add_of_mem v hv (aeval_mem_of_mem v hy p) (aeval_mem_of_mem v hy q), hp, hq]
  | mul_X p i hp => rw [map_mul, aeval_X, map_mul, aeval_X, v.evalAt_mul_of_mem hv (aeval_mem_of_mem v hy p) (hy i), hp]

theorem aeval_mul_of_isHomogeneous {a : ℕ} {q : MvPolynomial (Fin a) (AlgebraicClosure ℚ)} {m : ℕ}
    (hq : q.IsHomogeneous m) (c : F) (y : Fin a → F) :
    aeval (fun i => c * y i) q = c ^ m * aeval y q := by
  classical
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : d.degree = m := by
    by_contra hne
    exact (mem_support_iff.mp hd) (hq.coeff_eq_zero hne)
  rw [Finsupp.prod, Finsupp.prod]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have : ∑ i ∈ d.support, d i = m := by rw [← hdeg]; rfl
  rw [this]
  ring

end Generic

section Orders

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem ord_pivot_eq {r : ℕ} (hr : 0 < r) (f : Fin r → F) (hf : ∀ i, f i ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hfD : ∀ i, f i ∈ riemannRochSpace D)
    (v : Place (AlgebraicClosure ℚ) F) (hex : ∃ i, v.ord (f i) + D v = 0) :
    v.ord (f (pivotIndex f v hr)) = -D v := by
  obtain ⟨i, hi⟩ := hex
  apply le_antisymm
  · have := ord_pivot_le hr f v i; linarith
  · have := (mem_riemannRochSpace_iff.mp (hfD _) v).resolve_left (hf (pivotIndex f v hr)); linarith

theorem exists_ord_add_eq_zero_of_span {a b : ℕ} (s : Fin a → F) (u : Fin b → F) (hu : ∀ j, u j ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    (huD : ∀ j, u j ∈ riemannRochSpace D)
    (v : Place (AlgebraicClosure ℚ) F) (hbpf : ∃ j, v.ord (u j) + D v = 0) :
    ∃ i, v.ord (s i) + D v = 0 := by
  classical
  by_contra hnone
  push Not at hnone

  have hsub : ∀ i, s i ∈ riemannRochSpace (D - Finsupp.single v 1) := by
    intro i
    rw [mem_riemannRochSpace_iff]
    intro w
    rcases eq_or_ne (s i) 0 with h0 | h0
    · exact Or.inl h0
    right
    have hsi : s i ∈ riemannRochSpace D := by rw [← hsD]; exact Submodule.subset_span ⟨i, rfl⟩
    have hge := (mem_riemannRochSpace_iff.mp hsi w).resolve_left h0
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with hvw
    · subst hvw; have := hnone i; omega
    · rw [sub_zero]; exact hge
  have hle : Submodule.span (AlgebraicClosure ℚ) (Set.range s) ≤ riemannRochSpace (D - Finsupp.single v 1) := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hsub i
  obtain ⟨j, hj⟩ := hbpf
  have huj : u j ∈ riemannRochSpace (D - Finsupp.single v 1) := by
    apply hle; rw [hsD]; exact huD j
  have := (mem_riemannRochSpace_iff.mp huj v).resolve_left (hu j)
  rw [Finsupp.sub_apply, Finsupp.single_eq_same] at this
  omega

end Orders

end P2MBpf

namespace P2MBpf

open AlgebraicCurve ModularCurve MvPolynomial

section Easy

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {a b : ℕ}

theorem evalVec_eq_smul_linear (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (u : Fin b → F)
    (hs : ∀ i, s i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (M : Fin b → Fin a → AlgebraicClosure ℚ) (hM : ∀ j, ∑ i, M j i • s i = u j)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    (hord : v.ord (s (pivotIndex s v ha)) = v.ord (u (pivotIndex u v hb))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ evalVec u v = c • fun j => ∑ i, M j i * evalVec s v i := by
  set k := pivotIndex s v ha with hk
  set k' := pivotIndex u v hb with hk'
  have hrs : ∀ i, s i * (s k)⁻¹ ∈ v.toValuationSubring := fun i => ratio_pivot_mem ha s hs v i
  have hus : ∀ j, u j * (s k)⁻¹ = ∑ i, M j i • (s i * (s k)⁻¹) := by
    intro j
    rw [← hM j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc]
  have hus_mem : ∀ j, u j * (s k)⁻¹ ∈ v.toValuationSubring := fun j => by
    rw [hus j]; exact sum_smul_mem _ v _ hrs

  set w : F := s k * (u k')⁻¹ with hw
  have hw0 : w ≠ 0 := mul_ne_zero (hs k) (inv_ne_zero (hu k'))
  have hword : v.ord w = 0 := by rw [hw, v.ord_mul (hs k) (inv_ne_zero (hu k')), v.ord_inv]; omega
  have hwmem : w ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hw0 hword.ge
  have hwinv : w⁻¹ = u k' * (s k)⁻¹ := by rw [hw, mul_inv, inv_inv, mul_comm]
  have hwinv_mem : w⁻¹ ∈ v.toValuationSubring := by rw [hwinv]; exact hus_mem k'
  set c := v.evalAt w with hc
  have hcne : c ≠ 0 := by
    intro h0
    have h1 : v.evalAt (w * w⁻¹) = 1 := by rw [mul_inv_cancel₀ hw0, v.evalAt_one]
    rw [v.evalAt_mul_of_mem hv hwmem hwinv_mem, ← hc, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨c, hcne, ?_⟩
  funext j
  rw [Pi.smul_apply, smul_eq_mul, evalVec_apply hb u v j, ← hk']
  have hsplit : u j * (u k')⁻¹ = (u j * (s k)⁻¹) * w := by
    rw [hw]; field_simp [hs k, hu k']
  rw [hsplit, v.evalAt_mul_of_mem hv (hus_mem j) hwmem, ← hc, hus j, evalAt_sum_smul_of_mem _ v hv _ hrs, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [evalVec_apply ha s v i, ← hk]

theorem pointHt_le_of_linear (ha : 0 < a) (hb : 0 < b) (s : Fin a → F) (u : Fin b → F)
    (M : Fin b → Fin a → AlgebraicClosure ℚ) (v : Place (AlgebraicClosure ℚ) F)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) (hev : evalVec u v = c • fun j => ∑ i, M j i * evalVec s v i) :
    pointHt u v ≤ Real.log (Fintype.card (Fin a)) + absLogHeight (fun q : Fin b × Fin a => M q.1 q.2) + pointHt s v := by
  show absLogHeight (evalVec u v) ≤ _ + _ + absLogHeight (evalVec s v)
  rw [hev, absLogHeight_smul _ hc]
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact absLogHeight_linear_le M (evalVec s v)

end Easy

section CertAt

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {a b : ℕ}

theorem certificate_at (ha : 0 < a) (s : Fin a → F) (u : Fin b → F) (hs : ∀ i, s i ≠ 0)
    (M : Fin b → Fin a → AlgebraicClosure ℚ) (hM : ∀ j, ∑ i, M j i • s i = u j)
    {Mdeg : ℕ} (q : Fin a → Fin b → MvPolynomial (Fin a) (AlgebraicClosure ℚ))
    (hq : ∀ k j, (q k j).IsHomogeneous Mdeg)
    (hcert : ∀ k, ∑ j, aeval s (q k j) * u j = s k ^ (Mdeg + 1))
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) (k : Fin a) :
    ∑ j, MvPolynomial.eval (evalVec s v) (q k j) * (∑ i, M j i * evalVec s v i) = evalVec s v k ^ (Mdeg + 1) := by
  set kp := pivotIndex s v ha with hkp
  set r : F := (s kp)⁻¹ with hr
  have hr0 : r ≠ 0 := inv_ne_zero (hs kp)
  let y : Fin a → F := fun i => s i * r
  have hy : ∀ i, y i ∈ v.toValuationSubring := fun i => ratio_pivot_mem ha s hs v i
  have hx : ∀ i, evalVec s v i = v.evalAt (y i) := fun i => by rw [evalVec_apply ha s v i]

  have hfun : ∑ j, aeval y (q k j) * (∑ i, M j i • y i) = y k ^ (Mdeg + 1) := by
    have hscale : ∀ j, aeval y (q k j) = r ^ Mdeg * aeval s (q k j) := by
      intro j
      have := aeval_mul_of_isHomogeneous (F := F) (hq k j) r s
      rw [show (fun i => r * s i) = y from funext fun i => mul_comm _ _] at this
      exact this
    have hlin : ∀ j, ∑ i, M j i • y i = u j * r := by
      intro j
      rw [← hM j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc]
    simp_rw [hscale, hlin]
    have := congrArg (fun z => z * r ^ (Mdeg + 1)) (hcert k)
    simp only [Finset.sum_mul] at this
    rw [show y k ^ (Mdeg + 1) = s k ^ (Mdeg + 1) * r ^ (Mdeg + 1) by rw [← mul_pow]]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hmemq : ∀ j, aeval y (q k j) ∈ v.toValuationSubring := fun j => aeval_mem_of_mem v hy (q k j)
  have hmeml : ∀ j, (∑ i, M j i • y i) ∈ v.toValuationSubring := fun j => sum_smul_mem _ v _ hy
  have h1 := congrArg v.evalAt hfun
  rw [evalAt_sum_mul_of_mem _ v hv hmemq hmeml, evalAt_pow_of_mem v hv (hy k)] at h1
  simp_rw [evalAt_aeval_of_mem v hv hy, evalAt_sum_smul_of_mem _ v hv _ hy] at h1
  have hxf : evalVec s v = fun i => v.evalAt (y i) := funext hx
  rw [hxf]
  have h2 : ∀ j, MvPolynomial.eval (fun i => v.evalAt (y i)) (q k j) = aeval (fun i => v.evalAt (y i)) (q k j) :=
    fun j => rfl
  simp_rw [h2]
  simpa using h1

end CertAt

end P2MBpf

namespace P2MBpf

open AlgebraicCurve ModularCurve MvPolynomial

section Final

set_option maxHeartbeats 6400000 in
theorem main (N : ℕ) [NeZero N]
    {a b : ℕ} (s : Fin a → ↥(modularFunctionFieldBar N)) (u : Fin b → ↥(modularFunctionFieldBar N))
    (hs : ∀ i, s i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hd : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    (huD : ∀ j, u j ∈ riemannRochSpace D)
    (hbpf : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), ∃ j, w.ord (u j) + D w = 0) :
    ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), |pointHt s v - pointHt u v| ≤ C := by
  classical
  have hrat : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), v.IsRational := fun v =>
    (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)
  have hb : 0 < b := by obtain ⟨j, -⟩ := hbpf (cuspInftyBar N); exact j.pos
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · exfalso
      subst ha0
      obtain ⟨j, -⟩ := hbpf (cuspInftyBar N)
      have : u j ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by rw [hsD]; exact huD j
      rw [Set.range_eq_empty s, Submodule.span_empty, Submodule.mem_bot] at this
      exact hu j this
    · exact ha0
  have hMex : ∀ j, ∃ c : Fin a → AlgebraicClosure ℚ, ∑ i, c i • s i = u j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun _).mp (by rw [hsD]; exact huD j)
  choose Mmat hM using hMex
  obtain ⟨Mdeg, hc⟩ := ModularCurve.JZero.exists_isHomogeneous_sum_aeval_mul_eq_pow N s u hu D hd hsD huD hbpf
  choose q hq hcert using hc
  obtain ⟨C₁, hC₁⟩ := P2MBpfH.absLogHeight_le_of_certificate hb q hq Mmat
  refine ⟨max (Real.log (Fintype.card (Fin a)) + absLogHeight (fun p : Fin b × Fin a => Mmat p.1 p.2)) C₁, fun v => ?_⟩
  have hv := hrat v
  have hsD' : ∀ i, s i ∈ riemannRochSpace D := fun i => by rw [← hsD]; exact Submodule.subset_span ⟨i, rfl⟩
  have hordu : v.ord (u (pivotIndex u v hb)) = -D v := ord_pivot_eq hb u hu D huD v (hbpf v)
  have hords : v.ord (s (pivotIndex s v ha)) = -D v :=
    ord_pivot_eq ha s hs D hsD' v (exists_ord_add_eq_zero_of_span s u hu D hsD huD v (hbpf v))
  obtain ⟨c, hc0, hev⟩ := evalVec_eq_smul_linear ha hb s u hs hu Mmat hM v hv (by rw [hords, hordu])
  have h_easy := pointHt_le_of_linear ha hb s u Mmat v hc0 hev
  have h_hard : pointHt s v ≤ pointHt u v + C₁ :=
    hC₁ (evalVec s v) (evalVec u v) c hc0 (fun j => by rw [hev]; rfl)
      (fun k => certificate_at ha s u hs Mmat hM q hq hcert v hv k)
  have hm1 := le_max_left (Real.log (Fintype.card (Fin a)) + absLogHeight (fun p : Fin b × Fin a => Mmat p.1 p.2)) C₁
  have hm2 := le_max_right (Real.log (Fintype.card (Fin a)) + absLogHeight (fun p : Fin b × Fin a => Mmat p.1 p.2)) C₁
  rw [abs_le]
  constructor <;> linarith

end Final

end P2MBpf

open AlgebraicCurve ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    {a b : ℕ} (s : Fin a → ↥(ModularCurve.modularFunctionFieldBar N)) (u : Fin b → ↥(ModularCurve.modularFunctionFieldBar N))
    (hs : ∀ i, s i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hd : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = AlgebraicCurve.riemannRochSpace D)
    (huD : ∀ j, u j ∈ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ∃ j, w.ord (u j) + D w = 0) :
    ∃ C : ℝ, ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      |AlgebraicCurve.pointHt s v - AlgebraicCurve.pointHt u v| ≤ C :=
  P2MBpf.main N s u hs hu D hd hsD huD hbpf

end S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
end P2MW
export P2MW.S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero (solution)
