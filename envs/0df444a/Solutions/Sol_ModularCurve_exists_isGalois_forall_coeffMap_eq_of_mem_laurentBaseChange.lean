-- Prove2me | solution 1 for ModularCurve.exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/32947883-4dc2-5cae-87a1-78009b3d68e4

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange.ModularCurve IntermediateField"

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff coeffMap_mem_laurentBaseChange_of_ringHom"
p2m_open "ModularCurve"

private theorem coeffMap_algebraMap_const {K K' : Type*} [Field K] [Field K'] (f : K →+* K') (c : K) :
    coeffMap f (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (f c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem coeffMap_algebraMap_coeffEmb (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (z : LaurentSeries ℚ) :
    coeffMap (algebraMap E (AlgebraicClosure ℚ)) (coeffEmb E z) = coeffEmb (AlgebraicClosure ℚ) z := by
  show coeffMap _ (coeffMap (algebraMap ℚ E) z) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) z
  rw [coeffMap_coeffMap, ← IsScalarTower.algebraMap_eq ℚ E (AlgebraicClosure ℚ)]

private theorem exists_mem_laurentBaseChange_of_le (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {E₁ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : E₁ ≤ E₂) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : ∃ y : LaurentSeries E₁, y ∈ laurentBaseChange E₁ F₀ ∧ coeffMap (algebraMap E₁ (AlgebraicClosure ℚ)) y = x) :
    ∃ y : LaurentSeries E₂, y ∈ laurentBaseChange E₂ F₀ ∧ coeffMap (algebraMap E₂ (AlgebraicClosure ℚ)) y = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨coeffMap (IntermediateField.inclusion h).toRingHom y,
    coeffMap_mem_laurentBaseChange_of_ringHom _ F₀ hy, ?_⟩
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun _ => rfl) y

private theorem exists_finiteDimensional_mem_laurentBaseChange (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∃ y : LaurentSeries E, y ∈ laurentBaseChange E F₀ ∧ coeffMap (algebraMap E (AlgebraicClosure ℚ)) y = x := by
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hbot : FiniteDimensional ℚ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := inferInstance
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
    · refine ⟨IntermediateField.adjoin ℚ {c}, IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic c).isIntegral,
        algebraMap _ _ (⟨c, IntermediateField.mem_adjoin_simple_self ℚ c⟩ : IntermediateField.adjoin ℚ {c}),
        IntermediateField.algebraMap_mem _ _, ?_⟩
      rw [coeffMap_algebraMap_const]
      rfl
    · exact ⟨⊥, hbot, coeffEmb _ z, coeffEmb_mem_laurentBaseChange _ hz, coeffMap_algebraMap_coeffEmb ⊥ z⟩
  | one => exact ⟨⊥, hbot, 1, one_mem _, map_one _⟩
  | add x y _ _ hx hy =>
    obtain ⟨E₁, hE₁, hx⟩ := hx
    obtain ⟨E₂, hE₂, hy⟩ := hy
    haveI := hE₁
    haveI := hE₂
    obtain ⟨y₁, hy₁, rfl⟩ := exists_mem_laurentBaseChange_of_le F₀ (le_sup_left : E₁ ≤ E₁ ⊔ E₂) hx
    obtain ⟨y₂, hy₂, rfl⟩ := exists_mem_laurentBaseChange_of_le F₀ (le_sup_right : E₂ ≤ E₁ ⊔ E₂) hy
    exact ⟨E₁ ⊔ E₂, IntermediateField.finiteDimensional_sup E₁ E₂, y₁ + y₂, add_mem hy₁ hy₂, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨E, hE, y, hy, rfl⟩ := hx
    exact ⟨E, hE, -y, neg_mem hy, map_neg _ _⟩
  | inv x _ hx =>
    obtain ⟨E, hE, y, hy, rfl⟩ := hx
    exact ⟨E, hE, y⁻¹, inv_mem hy, map_inv₀ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨E₁, hE₁, hx⟩ := hx
    obtain ⟨E₂, hE₂, hy⟩ := hy
    haveI := hE₁
    haveI := hE₂
    obtain ⟨y₁, hy₁, rfl⟩ := exists_mem_laurentBaseChange_of_le F₀ (le_sup_left : E₁ ≤ E₁ ⊔ E₂) hx
    obtain ⟨y₂, hy₂, rfl⟩ := exists_mem_laurentBaseChange_of_le F₀ (le_sup_right : E₂ ≤ E₁ ⊔ E₂) hy
    exact ⟨E₁ ⊔ E₂, IntermediateField.finiteDimensional_sup E₁ E₂, y₁ * y₂, mul_mem hy₁ hy₂, map_mul _ _ _⟩

end ModularCurve

theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {ι : Type} [Finite ι]
    (x : ι → LaurentSeries (AlgebraicClosure ℚ))
    (hx : ∀ i, x i ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧ IsGalois ℚ E ∧
      ∃ y : ι → LaurentSeries E, (∀ i, y i ∈ laurentBaseChange E F₀) ∧
        ∀ i, coeffMap (algebraMap E (AlgebraicClosure ℚ)) (y i) = x i := by
  classical
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  choose E hEfd hy using fun i =>
    ModularCurve.exists_finiteDimensional_mem_laurentBaseChange F₀ (x i) (hx i)
  haveI : ∀ i, FiniteDimensional ℚ (E i) := hEfd
  haveI : FiniteDimensional ℚ (⨆ i, E i : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  have hfd : FiniteDimensional ℚ (normalClosure ℚ (⨆ i, E i : IntermediateField ℚ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)) :=
    normalClosure.is_finiteDimensional ℚ _ _
  haveI := hfd
  have hle : ∀ i, E i ≤ normalClosure ℚ (⨆ i, E i : IntermediateField ℚ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) :=
    fun i => (le_iSup E i).trans (IntermediateField.le_normalClosure _)
  choose y hy₁ hy₂ using fun i => ModularCurve.exists_mem_laurentBaseChange_of_le F₀ (hle i) (hy i)
  refine ⟨normalClosure ℚ (⨆ i, E i : IntermediateField ℚ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ), hfd, ?_, y, hy₁, hy₂⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := normal_iff.mpr fun z =>
    ⟨(Algebra.IsAlgebraic.isAlgebraic z).isIntegral, IsAlgClosed.splits _⟩
  haveI : Normal ℚ (normalClosure ℚ (⨆ i, E i : IntermediateField ℚ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ _ _
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

end S_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange (solution)
