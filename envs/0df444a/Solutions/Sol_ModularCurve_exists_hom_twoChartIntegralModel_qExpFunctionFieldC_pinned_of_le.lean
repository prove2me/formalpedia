-- Prove2me | solution 1 for ModularCurve.exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/59aa9d91-d9fc-5f7b-88bd-21d0adebf893

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve
open scoped MatrixGroups

namespace PiH

theorem coe_algebraMap_base (p : ℕ) (Δ : Subgroup SL(2, ℤ)) (r : ↥(GaloisRep.ratLocalizedAt p)) :
    ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Δ) r : ↥(qExpFunctionFieldC ℚ Δ)) : LaurentSeries ℚ) = ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r : ℚ) : LaurentSeries ℚ) := by
  rw [IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Δ)]
  simp

def incl (p : ℕ) {Γ Γ' : Subgroup SL(2, ℤ)} (hΓ : Γ ≤ Γ') : ↥(qExpFunctionFieldC ℚ Γ') →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(qExpFunctionFieldC ℚ Γ) where
  toFun y := ⟨(y : LaurentSeries ℚ), qExpFunctionFieldC_mono ℚ hΓ y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by rw [coe_algebraMap_base, coe_algebraMap_base])

theorem coe_incl (p : ℕ) {Γ Γ' : Subgroup SL(2, ℤ)} (hΓ : Γ ≤ Γ') (y : ↥(qExpFunctionFieldC ℚ Γ')) :
    ((incl p hΓ y : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = (y : LaurentSeries ℚ) :=
  @Subtype.coe_mk (LaurentSeries ℚ) (· ∈ qExpFunctionFieldC ℚ Γ) (y : LaurentSeries ℚ) (qExpFunctionFieldC_mono ℚ hΓ y.2)

theorem adjoin_singleton_inv_eq {K L : Type*} [Field K] [Field L] [Algebra K L] (s : L) :
    IntermediateField.adjoin K ({s⁻¹} : Set L) = IntermediateField.adjoin K ({s} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr ((IntermediateField.adjoin K _).inv_mem (IntermediateField.mem_adjoin_simple_self K s))
  · have h1 := (IntermediateField.adjoin K ({s⁻¹} : Set L)).inv_mem (IntermediateField.mem_adjoin_simple_self K s⁻¹)
    rw [inv_inv] at h1
    rw [IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr h1

theorem isAlgebraic_adjoin_inv {K L : Type*} [Field K] [Field L] [Algebra K L] (s : L)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({s} : Set L)) L] :
    Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({s⁻¹} : Set L)) L := by
  rw [adjoin_singleton_inv_eq]; exact Algebra.IsAlgebraic.of_finite _ _

theorem adjoin_singleton_subset_subfield {K L : Type*} [Field K] [Field L] [Algebra K L] (s : L) (T : Subfield L)
    (hs : s ∈ T) (hK : ∀ k : K, algebraMap K L k ∈ T) :
    ∀ x ∈ IntermediateField.adjoin K ({s} : Set L), x ∈ T := by
  intro x hx
  have hx' : x ∈ (IntermediateField.adjoin K ({s} : Set L)).toSubfield := hx
  rw [IntermediateField.adjoin_toSubfield] at hx'
  refine (Subfield.closure_le.mpr ?_) hx'
  rintro y (⟨k, rfl⟩ | hy)
  · exact hK k
  · obtain rfl := hy; exact hs

theorem ringHom_finite_of_finiteDimensional_of_lift {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional ↥E L]
    (φ : L' →+* L) (ψ : ↥E →+* L') (hψ : ∀ e : ↥E, φ (ψ e) = (e : L)) : φ.Finite := by
  letI : Algebra ↥E L' := ψ.toAlgebra
  letI : Algebra L' L := φ.toAlgebra
  haveI : IsScalarTower ↥E L' L := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  exact Module.Finite.of_restrictScalars_finite ↥E L' L

end PiH

open PiH in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (Γ Γ' : Subgroup SL(2, ℤ)) (hΓ : Γ ≤ Γ') [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (j : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (j' : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ')) [Fact (j' ≠ 0)] (hj' : (j' : LaurentSeries ℚ) = ModularCurve.jqModC ℚ) :
    ∃ (π : TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ⟶
            TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j')
      (iota0 : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j')
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j))
      (iotaInf : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j')
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j)),
      π ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j' =
        TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ∧
      (∀ b, (((iota0 b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j))
              : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
        ((b : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ')) : LaurentSeries ℚ)) ∧
      TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ≫ π =
        Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j' ∧
      (∀ b, (((iotaInf b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j))
              : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
        ((b : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ')) : LaurentSeries ℚ)) ∧
      TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ≫ π =
        Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j' ∧
      IsFinite π ∧ Function.Surjective π.base ∧
      π ⁻¹ᵁ (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j').opensRange =
        (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j).opensRange := by
  classical
  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hT' : ModularGroup.T ∈ Γ' := hΓ hT

  have hjj : ((j' : ↥(qExpFunctionFieldC ℚ Γ')) : LaurentSeries ℚ) = ((j : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := hj'.trans hj.symm

  have hIST : ∀ Δ : Subgroup SL(2, ℤ), @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Δ) _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Δ)).toSMul _ := fun Δ =>
    @IsScalarTower.of_algebraMap_eq' ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Δ) _ _ _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Δ)) _
      (RingHom.ext fun r => by
        show ((r : ℚ) : ↥(qExpFunctionFieldC ℚ Δ)) = @algebraMap ℚ ↥(qExpFunctionFieldC ℚ Δ) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Δ)) (r : ℚ)
        exact (eq_ratCast _ _).symm)

  have hFD := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ hT Γ le_rfl
      (fun γ h => Or.inl h) j hj).1
  have hFD' := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ Γ' hT' Γ' le_rfl
      (fun γ h => Or.inl h) j' hj').1

  obtain ⟨hFTfin', hFTinf'⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p Γ' hT' j' hj'
  haveI := hFTfin'
  haveI := hFTinf'
  haveI := hFD'
  have hFfin : IsNoetherianRing ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ') j') ∧
      IsFractionRing ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ') j') ↥(qExpFunctionFieldC ℚ Γ') := by
    refine ⟨Algebra.FiniteType.isNoetherianRing ↥(GaloisRep.ratLocalizedAt p) _, ?_⟩
    exact @AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg ↥(GaloisRep.ratLocalizedAt p) _ _ ℚ _ _ _
      ↥(qExpFunctionFieldC ℚ Γ') _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ')) (hIST Γ')
      {(j' : ↥(qExpFunctionFieldC ℚ Γ'))} (Algebra.IsAlgebraic.of_finite _ _)
  have hFinf : IsNoetherianRing ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ') j') ∧
      IsFractionRing ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ') j') ↥(qExpFunctionFieldC ℚ Γ') := by
    refine ⟨Algebra.FiniteType.isNoetherianRing ↥(GaloisRep.ratLocalizedAt p) _, ?_⟩
    exact @AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg ↥(GaloisRep.ratLocalizedAt p) _ _ ℚ _ _ _
      ↥(qExpFunctionFieldC ℚ Γ') _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ')) (hIST Γ')
      {(j' : ↥(qExpFunctionFieldC ℚ Γ'))⁻¹}
      (@isAlgebraic_adjoin_inv ℚ ↥(qExpFunctionFieldC ℚ Γ') _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ')) _ hFD')

  let φ : ↥(qExpFunctionFieldC ℚ Γ') →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(qExpFunctionFieldC ℚ Γ) := incl p hΓ
  have hφj : φ j' = j := Subtype.ext ((coe_incl p hΓ j').trans hjj)
  have hφfin : φ.toRingHom.Finite := by

    let T : Subfield ↥(qExpFunctionFieldC ℚ Γ) :=
      Subfield.comap (qExpFunctionFieldC ℚ Γ).toSubfield.subtype (qExpFunctionFieldC ℚ Γ').toSubfield
    have hT : ∀ y : ↥(qExpFunctionFieldC ℚ Γ), y ∈ T ↔ (y : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ Γ' := fun y => Iff.rfl
    have hjT : (j : ↥(qExpFunctionFieldC ℚ Γ)) ∈ T := by rw [hT, ← hjj]; exact j'.2
    have hKT : ∀ k : ℚ, @algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)) k ∈ T :=
      fun k => (hT _).mpr ((qExpFunctionFieldC ℚ Γ').algebraMap_mem k)
    have hle := @adjoin_singleton_subset_subfield ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ))
      (j : ↥(qExpFunctionFieldC ℚ Γ)) T hjT hKT
    let ψ : ↥(@IntermediateField.adjoin ℚ _ ↥(qExpFunctionFieldC ℚ Γ) _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ))
        ({(j : ↥(qExpFunctionFieldC ℚ Γ))} : Set ↥(qExpFunctionFieldC ℚ Γ))) →+* ↥(qExpFunctionFieldC ℚ Γ') :=
      { toFun := fun e => ⟨((e : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ), (hT _).mp (hle _ e.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }
    haveI := hFD
    refine @ringHom_finite_of_finiteDimensional_of_lift ℚ ↥(qExpFunctionFieldC ℚ Γ) ↥(qExpFunctionFieldC ℚ Γ') _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)) _ hFD φ.toRingHom ψ (fun e => Subtype.ext ?_)
    show ((incl p hΓ (ψ e) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = ((e : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)
    rw [coe_incl]
    rfl

  obtain ⟨m, ιF, ιI, hιF, hιI, hmb, hmF, hmI, hmFin, -, hfin, hsurj⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_hom_isFinite_surjective_of_algHom ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ') ↥(qExpFunctionFieldC ℚ Γ) φ hφfin j' j hφj hFfin hFinf
  refine ⟨m, ιF, ιI, hmb, ?_, hmF.symm, ?_, hmI.symm, hfin, hsurj, hmFin⟩
  · intro b
    have h := congrArg (fun z : ↥(qExpFunctionFieldC ℚ Γ) => (z : LaurentSeries ℚ)) (hιF b)
    exact h.trans (coe_incl p hΓ b)
  · intro b
    have h := congrArg (fun z : ↥(qExpFunctionFieldC ℚ Γ) => (z : LaurentSeries ℚ)) (hιI b)
    exact h.trans (coe_incl p hΓ b)

end S_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
end P2MW
export P2MW.S_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le (solution)
