-- Prove2me | solution 1 for ModularCurve.XOneP.finrank_H0_sectionsOf_eq_one_and_finrank_H1_eq_genusFF_pullback_toBase_of_isAlgClosed_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7e5c7e24-4ff0-5fd6-a0c8-9f4238707838

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_finrank_H0_sectionsOf_eq_one_and_finrank_H1_eq_genusFF_pullback_toBase_of_isAlgClosed_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XOneP_finrank_H0_sectionsOf_eq_one_and_finrank_H1_eq_genusFF_pullback_toBase_of_isAlgClosed_twoChartIntegralModel_x1_mul.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset x1FunctionField jq coeffEmb laurentBaseChange jqModC jqModC_rat map_jqModC baseChangeHom baseChangeHom_mem baseChangeEquiv isFractionRing_tensorProduct_laurentBaseChange laurentBaseChange_qExpFunctionFieldC_eq genusFF_qExpFunctionFieldC_eq_of_ringHom finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index jqModC_mem_intFormRatiosC transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange"
namespace XOneP
namespace GenFibre
p2m_open "ModularCurve"

theorem isProper_pullback_snd_toBase
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (L' : Type) [Field L'] [Algebra A L'] :
    IsProper (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI : IsProper (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) :=
    ModularCurve.isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK A j hj
  infer_instance

theorem smoothOfRelativeDimension_one_pullback_snd_toBase
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (L' : Type) [Field L'] [IsAlgClosed L'] [Algebra L L'] [Algebra A L'] [IsScalarTower A L L'] :
    SmoothOfRelativeDimension 1 (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  exact AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
    A L (↥K) j htj hFD hsep L'

theorem isDomain_tensorProduct_subalgebra
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (L' : Type) [Field L'] [Algebra L L'] [Algebra A L'] [IsScalarTower A L L']
    (𝒪 : Subalgebra A ↥K) :
    IsDomain (L' ⊗[A] ↥𝒪) := by
  subst hK

  haveI : Module.Flat A L := IsLocalization.flat L (nonZeroDivisors A)
  haveI : Module.Flat A L' := Module.Flat.trans A L L'

  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective
  haveI : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L

  let e₁ : L' ⊗[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) ≃ₐ[L'] L' ⊗[L] (L ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))) :=
    Algebra.TensorProduct.congr AlgEquiv.refl (ModularCurve.baseChangeEquiv L (ModularCurve.x1FunctionField (M * p))).symm
  let e₂ : L' ⊗[L] (L ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))) ≃ₐ[L'] L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)) := Algebra.TensorProduct.cancelBaseChange ℚ L L' L' ↥(ModularCurve.x1FunctionField (M * p))
  haveI hdomL : IsDomain (L' ⊗[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) :=
    (e₁.trans e₂).injective.isDomain (e₁.trans e₂).toAlgHom.toRingHom

  haveI hdomA : IsDomain (L' ⊗[A] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) :=
    (IsLocalization.algebraTensorEquiv (nonZeroDivisors A) L L' ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))).symm.injective.isDomain
      (IsLocalization.algebraTensorEquiv (nonZeroDivisors A) L L' ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))).symm.toAlgHom.toRingHom

  let ι := Algebra.TensorProduct.map (AlgHom.id A L') 𝒪.val
  have hlt : ∀ z, LinearMap.lTensor L' 𝒪.val.toLinearMap z = ι z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hι : Function.Injective ι := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L') 𝒪.val.toLinearMap Subtype.val_injective
    intro x y hxy
    exact h ((hlt x).trans (hxy.trans (hlt y).symm))
  exact hι.isDomain ι

theorem isIntegral_pullback_toBase
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (L' : Type) [Field L'] [IsAlgClosed L'] [Algebra L L'] [Algebra A L'] [IsScalarTower A L L'] :
    IsIntegral (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))) := by
  haveI := isDomain_tensorProduct_subalgebra p M L K hK A L' (TwoChartIntegralModel.chartAlgFin A (↥K) j)
  haveI := isDomain_tensorProduct_subalgebra p M L K hK A L' (TwoChartIntegralModel.chartAlgInf A (↥K) j)
  haveI : Nontrivial (L' ⊗[A] ↥(TwoChartIntegralModel.chartAlgMid A (↥K) j)) :=
    (isDomain_tensorProduct_subalgebra p M L K hK A L' (TwoChartIntegralModel.chartAlgMid A (↥K) j)).toNontrivial
  exact AlgebraicCurve.TwoChartIntegralModel.isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg A (↥K) j L'

end ModularCurve.XOneP.GenFibre

namespace ModularCurve p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset x1FunctionField jq coeffEmb laurentBaseChange jqModC jqModC_rat map_jqModC baseChangeHom baseChangeHom_mem baseChangeEquiv isFractionRing_tensorProduct_laurentBaseChange laurentBaseChange_qExpFunctionFieldC_eq genusFF_qExpFunctionFieldC_eq_of_ringHom finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index jqModC_mem_intFormRatiosC transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange" namespace XOneP namespace GenFibre end ModularCurve.XOneP.GenFibre
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.XOneP.GenFibre.exists_transcendental_finiteDimensional_qExpFunctionFieldC_gamma1
    (N : ℕ) [NeZero N] (K : Type) [Field K] [CharZero K] :
    ∃ x : ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 N), Transcendental K x ∧
      FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 N))))
        (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 N)) := by
  let x : ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 N) :=
    ⟨ModularCurve.jqModC K, ModularCurve.intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)⟩
  have hx : (x : LaurentSeries K) = ModularCurve.jqModC K := rfl
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  refine ⟨x, ?_, (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (CongruenceSubgroup.Gamma1 N) hT (CongruenceSubgroup.Gamma1 N) le_rfl (fun γ hγ => Or.inl hγ) x hx).1⟩

  have hj : (x : LaurentSeries K) = ModularCurve.coeffEmb K ModularCurve.jq := by
    rw [hx, ← ModularCurve.jqModC_rat]
    exact (ModularCurve.map_jqModC (algebraMap ℚ K)).symm
  exact ModularCurve.transcendental_of_coe_eq_coeffEmb_jq K (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 N)) K x hj

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.XOneP.GenFibre.genusFF_laurentBaseChange_eq_algebraicClosure
    (N : ℕ) [NeZero N] (L' : Type) [Field L'] [CharZero L'] [IsAlgClosed L'] :
    AlgebraicCurve.genusFF L' ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField N)) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N))) := by
  show AlgebraicCurve.genusFF L' ↥(ModularCurve.laurentBaseChange L' (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N))) = _
  rw [ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq L' (CongruenceSubgroup.Gamma1 N),
    ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 N)]
  let φ : AlgebraicClosure ℚ →ₐ[ℚ] L' := IsAlgClosed.lift
  exact ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom φ.toRingHom (CongruenceSubgroup.Gamma1 N)
    (ModularCurve.XOneP.GenFibre.exists_transcendental_finiteDimensional_qExpFunctionFieldC_gamma1 N (AlgebraicClosure ℚ))

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.XOneP.GenFibre.nonempty_algEquiv_functionField_laurentBaseChange
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (L' : Type) [Field L'] [CharZero L'] [IsAlgClosed L'] [Algebra L L'] [Algebra A L'] [IsScalarTower A L L']
    [IsIntegral ↑(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L'))))] :
    letI := (AlgebraicCurve.baseToFunctionField (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L'))))).toAlgebra
    Nonempty ((pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A L')))).functionField ≃ₐ[L']
      ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p)))) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  set tb := AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j with htb
  set sL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A L')) with hsL'
  set sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A L)) with hsL
  set sLL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom (algebraMap L L')) with hsLL'
  letI algL' : Algebra L' (pullback tb sL').functionField :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd tb sL')).toAlgebra
  show Nonempty ((pullback tb sL').functionField ≃ₐ[L'] ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))))

  obtain ⟨es, hes, hsnd⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_isFractionRing A L (↥K) j
  haveI hintL : IsIntegral ↑(pullback tb sL) := IsIntegral.of_isIso es
  letI algL : Algebra L (pullback tb sL).functionField :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd tb sL)).toAlgebra
  letI algG : Algebra L (AlgebraicCurve.CurveModel.glued L j).functionField :=
    (AlgebraicCurve.baseToFunctionField (AlgebraicCurve.CurveModel.gluedToBase L j)).toAlgebra
  obtain ⟨eg⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
    (AlgebraicCurve.CurveModel.gluedToBase L j) (pullback.snd tb sL) (asIso es) hsnd
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  let eK : ↥K ≃ₐ[L] (AlgebraicCurve.CurveModel.glued L j).functionField :=
    AlgEquiv.ofRingEquiv (f := AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv L j)
      (AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv_algebraMap L j)
  let eL : ↥K ≃ₐ[L] (pullback tb sL).functionField := eK.trans eg

  have hcomp : sLL' ≫ sL = sL' := by
    rw [hsLL', hsL, hsL', ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A L L']
  let φ : pullback (pullback.snd tb sL) sLL' ≅ pullback tb sL' :=
    pullbackLeftPullbackSndIso tb sL sLL' ≪≫ pullback.congrHom rfl hcomp
  have hφsnd : φ.hom ≫ pullback.snd tb sL' = pullback.snd (pullback.snd tb sL) sLL' := by
    simp [φ]
    erw [pullback.lift_snd]
    simp
  haveI hintLL' : IsIntegral ↑(pullback (pullback.snd tb sL) sLL') := IsIntegral.of_isIso φ.inv
  letI algLL' : Algebra L' (pullback (pullback.snd tb sL) sLL').functionField :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd (pullback.snd tb sL) sLL')).toAlgebra
  obtain ⟨eφ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
    (pullback.snd (pullback.snd tb sL) sLL') (pullback.snd tb sL') φ hφsnd

  obtain ⟨Φ, hΦinj, hΦfrac, -⟩ :=
    AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing L' (pullback.snd tb sL)

  haveI : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L
  let g : (L ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))) ≃ₐ[L] (pullback tb sL).functionField :=
    (ModularCurve.baseChangeEquiv L (ModularCurve.x1FunctionField (M * p))).trans
      ((IntermediateField.equivOfEq hK.symm).trans eL)
  let γ : (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))) ≃ₐ[L'] L' ⊗[L] (pullback tb sL).functionField :=
    (Algebra.TensorProduct.cancelBaseChange ℚ L L' L' ↥(ModularCurve.x1FunctionField (M * p))).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L' ≃ₐ[L'] L') g)

  letI algΦ : Algebra (L' ⊗[L] (pullback tb sL).functionField) (pullback (pullback.snd tb sL) sLL').functionField :=
    Φ.toRingHom.toAlgebra
  haveI hfracΦ : IsFractionRing (L' ⊗[L] (pullback tb sL).functionField)
      (pullback (pullback.snd tb sL) sLL').functionField := hΦfrac
  letI algT : Algebra (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))) (pullback (pullback.snd tb sL) sLL').functionField :=
    ((algebraMap (L' ⊗[L] (pullback tb sL).functionField) (pullback (pullback.snd tb sL) sLL').functionField).comp
      γ.symm.toRingEquiv.symm.toRingHom).toAlgebra
  haveI hfracT : IsFractionRing (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      (pullback (pullback.snd tb sL) sLL').functionField :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (R := L' ⊗[L] (pullback tb sL).functionField)
      (S := (pullback (pullback.snd tb sL) sLL').functionField) (h := γ.symm.toRingEquiv)).mp hfracΦ

  letI algψ : Algebra (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))) :=
    ((ModularCurve.baseChangeHom L' (ModularCurve.x1FunctionField (M * p))).codRestrict
      (ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))).toSubalgebra
      (ModularCurve.baseChangeHom_mem L' (ModularCurve.x1FunctionField (M * p)))).toRingHom.toAlgebra
  haveI hfracψ : IsFractionRing (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))) :=
    ModularCurve.isFractionRing_tensorProduct_laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))

  haveI : IsScalarTower L' (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))) :=
    by
    refine IsScalarTower.of_algebraMap_eq (R := L') (S := L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      (A := ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p)))) (fun a => ?_)
    apply Subtype.ext
    change algebraMap L' (LaurentSeries L') a =
      ModularCurve.baseChangeHom L' (ModularCurve.x1FunctionField (M * p))
        (algebraMap L' (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))) a)
    exact ((ModularCurve.baseChangeHom L' (ModularCurve.x1FunctionField (M * p))).commutes a).symm
  have hγ : ∀ x, γ.symm.toRingEquiv.symm x = γ x := fun x => by
    rw [RingEquiv.symm_apply_eq]; simp
  haveI : IsScalarTower L' (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      (pullback (pullback.snd tb sL) sLL').functionField :=
    by
    refine IsScalarTower.of_algebraMap_eq (R := L') (S := L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))
      (A := (pullback (pullback.snd tb sL) sLL').functionField) (fun a => ?_)
    change algebraMap L' _ a = Φ (γ.symm.toRingEquiv.symm (algebraMap L' _ a))
    rw [hγ, AlgEquiv.commutes, AlgHom.commutes]
  let eT : (pullback (pullback.snd tb sL) sLL').functionField ≃ₐ[L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p))]
      ↥(ModularCurve.laurentBaseChange L' (ModularCurve.x1FunctionField (M * p))) :=
    IsLocalization.algEquiv (nonZeroDivisors (L' ⊗[ℚ] ↥(ModularCurve.x1FunctionField (M * p)))) _ _
  exact ⟨eφ.symm.trans (eT.restrictScalars L')⟩

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (L' : Type) [Field L'] [IsAlgClosed L'] [Algebra L L'] [Algebra A L'] [IsScalarTower A L L']
    (𝒲 : (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))).TwoAffineOpenCover) :
    Module.finrank L' (𝒲.sectionsOf (pullback.snd _ _)
        (SheafOfModules.unit (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A L')))).ringCatSheaf)).H0 = 1 ∧
    Module.finrank L' (𝒲.sectionsOf (pullback.snd _ _)
        (SheafOfModules.unit (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A L')))).ringCatSheaf)).H1 =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * p)))) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective

  haveI : IsProper (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))) :=
    ModularCurve.XOneP.GenFibre.isProper_pullback_snd_toBase p M L K hK A j hj L'
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))) :=
    ModularCurve.XOneP.GenFibre.smoothOfRelativeDimension_one_pullback_snd_toBase p M L K hK A j hj L'
  haveI : IsIntegral ↑(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))) :=
    ModularCurve.XOneP.GenFibre.isIntegral_pullback_toBase p M L K hK A j hj L'

  obtain ⟨-, -, h0, h1⟩ := AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed 𝒲
    (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A L'))))
  obtain ⟨e0, e1, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_unit_equiv_structureSheafSections 𝒲
      (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A L'))))

  letI : Algebra L' (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L')))).functionField :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L'))))).toAlgebra
  obtain ⟨e⟩ := ModularCurve.XOneP.GenFibre.nonempty_algEquiv_functionField_laurentBaseChange p M L K hK A j hj L'
  refine ⟨by rw [e0.finrank_eq, h0], ?_⟩
  rw [e1.finrank_eq, h1, ← ModularCurve.XOneP.GenFibre.genusFF_laurentBaseChange_eq_algebraicClosure (M * p) L']
  exact AlgebraicCurve.genusFF_eq_of_algEquiv e

#print axioms solution

end S_ModularCurve_XOneP_finrank_H0_sectionsOf_eq_one_and_finrank_H1_eq_genusFF_pullback_toBase_of_isAlgClosed_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_finrank_H0_sectionsOf_eq_one_and_finrank_H1_eq_genusFF_pullback_toBase_of_isAlgClosed_twoChartIntegralModel_x1_mul (solution)
