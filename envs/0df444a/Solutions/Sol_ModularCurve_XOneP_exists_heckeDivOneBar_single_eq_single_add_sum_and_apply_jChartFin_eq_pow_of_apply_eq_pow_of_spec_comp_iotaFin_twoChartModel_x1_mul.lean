-- Prove2me | solution 1 for ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b6ed32b3-7dd3-5f41-b4b9-dbf226737640

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_single_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber
import Theorems.Thm_ModularCurve_mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
import Theorems.Thm_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq
import Theorems.Thm_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul
import Theorems.Thm_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot
import Theorems.Thm_Polynomial_Monic_map_roots_eq_of_map_eq_kroneckerFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve P2MW.S_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong finrankAlong Divisor.correspondence Divisor.correspondence_apply Divisor.pullbackAlong_single SeparableAlong Place.mem_fiber Place Divisor HasPrincipalDivisors CurveModel IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.evalAt_one Place.evalAt_mul_of_mem Place.evalAt_algebraMap_eq fundamentalIdentityAlong separableAlong_of_charZero Divisor.exists_pullbackAlong_single_one_eq_sum Divisor.pushforwardAlong_single_one Place.evalAt_algebraMap_eq_evalAt_restrict Place.evalAt_norm_eq_prod_fiber"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndex ramificationIndex_pos restrict mem_restrict_iff restrictResidueMap restrictResidueMap_residue fiber mem_fiber ext ResidueField deg ord ord_coe_unit ord_unit_smul_zpow algebraMap_mem' toValuationSubring deg_eq_one_of_isAlgClosed_of_finite IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one evalAt_mul_of_mem evalAt_algebraMap_eq evalAt_algebraMap_eq_evalAt_restrict evalAt_norm_eq_prod_fiber"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F']

variable (F) in
theorem sheetSort_finite_residueField_restrict (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by
  have h := ValuationSubring.sum_finrank_residueField_le_finrank_of_forall_mem_iff
    (E := F) (F := F') (w.restrict F).toValuationSubring (ι := Unit) (fun _ => w.toValuationSubring)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ => w.mem_restrict_iff.symm)
    (fun _ a => by
      change restrictResidueMap F w (IsLocalRing.residue _ a) = _
      rw [restrictResidueMap_residue]
      rfl)
  exact h.1 ()

variable (F) in
theorem sheetSort_finite_residueField_of_isCurveOver [IsCurveOver K F] (w : Place K F') :
    Module.Finite K w.ResidueField := by
  haveI := IsCurveOver.finiteResidue (K := K) (w.restrict F)
  haveI := sheetSort_finite_residueField_restrict F w
  exact Module.Finite.trans (w.restrict F).ResidueField w.ResidueField

omit [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] in

theorem sheetSort_isRational_of_finite [IsAlgClosed K] (v : Place K F) [Module.Finite K v.ResidueField] :
    v.IsRational := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

omit [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] in

theorem sheetSort_evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

omit [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] in
theorem sheetSort_evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

omit [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] in
theorem sheetSort_evalAt_sum (v : Place K F) (hv : v.IsRational) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ s, f i) = ∑ i ∈ s, v.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, sheetSort_evalAt_zero]
  | insert a s ha ih =>
    have hs : ∑ i ∈ s, f i ∈ v.toValuationSubring :=
      Subring.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sheetSort_evalAt_add v hv (hf a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

omit [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] in

theorem sheetSort_ord_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have : f = ((u : v.toValuationSubring) : F) := (congrArg Subtype.val hu).symm
  rw [this]
  exact v.ord_coe_unit u

end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaOneBar coe_heckeAlphaOneBar HeckeBetaOneDefined heckeBetaOneBar coe_heckeBetaOneBar HeckeAlphaOneBarIntegral HeckeBetaOneBarIntegral heckeDivOneBar x1FunctionField x1x0FunctionFieldC x1FunctionFieldBar JOne arithmeticGalois qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq ModularPolynomialData coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange TwoChart.adjoin_le_chartAlg TwoChart.chartAlgFin TwoChart.jChartFin TwoChart.ιFin TwoChart.modelTo jqModC jqModC_rat map_jqModC qTwist qTwist_coeff qTwist_single qTwist_one_apply isCurveOver_x1FunctionFieldBar finrankAlong_heckeBetaOneBar mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq XOneP.exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul XOneP.mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul nonempty_modularPolynomialData modularPolynomial_kronecker PhiGen.splits_prime_at_slot_of_isPrimitiveRoot"
p2m_open "ModularCurve"

theorem sheetSort_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem sheetSort_coeffMap_qTwist {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ)
    (x : LaurentSeries R) : coeffMap f (qTwist u x) = qTwist (Units.map (f : R →* S) u) (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul]
  congr 1
  rw [← map_zpow, Units.coe_map, MonoidHom.coe_coe]

theorem sheetSort_qTwist_C {R : Type*} [CommRing R] (u : Rˣ) (c : R) :
    qTwist u (HahnSeries.C c) = HahnSeries.C c := by
  rw [HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]

end ModularCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong finrankAlong Divisor.correspondence Divisor.correspondence_apply Divisor.pullbackAlong_single SeparableAlong Place.mem_fiber Place Divisor HasPrincipalDivisors CurveModel IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.evalAt_one Place.evalAt_mul_of_mem Place.evalAt_algebraMap_eq fundamentalIdentityAlong separableAlong_of_charZero Divisor.exists_pullbackAlong_single_one_eq_sum Divisor.pushforwardAlong_single_one Place.evalAt_algebraMap_eq_evalAt_restrict Place.evalAt_norm_eq_prod_fiber"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndex ramificationIndex_pos restrict mem_restrict_iff restrictResidueMap restrictResidueMap_residue fiber mem_fiber ext ResidueField deg ord ord_coe_unit ord_unit_smul_zpow algebraMap_mem' toValuationSubring deg_eq_one_of_isAlgClosed_of_finite IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one evalAt_mul_of_mem evalAt_algebraMap_eq evalAt_algebraMap_eq_evalAt_restrict evalAt_norm_eq_prod_fiber"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem sheetSort_ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem sheetSort_mem_restrictAlong_iff [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem sheetSort_evalAt_restrictAlong [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (hv : (w.restrictAlong φ hφ).IsRational) {g : F}
    (hg : g ∈ (w.restrictAlong φ hφ).toValuationSubring) :
    w.evalAt (φ g) = (w.restrictAlong φ hφ).evalAt g := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.evalAt_algebraMap_eq_evalAt_restrict w hv hg

end AlgebraicCurve.Place

namespace SheetSort

theorem card_filter_eq_of_sum_single_eq {ι X : Type*} [Fintype ι] [DecidableEq X]
    (W : ι → X) (S : Finset X) (e : X → ℕ)
    (h : ∑ i, Finsupp.single (W i) (1 : ℤ) = ∑ w ∈ S, Finsupp.single w (e w : ℤ)) (x : X) :
    (Finset.univ.filter fun i => W i = x).card = if x ∈ S then e x else 0 := by
  classical
  have h1 := congrArg (fun D : X →₀ ℤ => D x) h
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply] at h1
  rw [Finset.sum_boole, Finset.sum_ite_eq'] at h1
  split_ifs at h1 with hx
  · rw [if_pos hx]; exact_mod_cast h1
  · rw [if_neg hx]; exact_mod_cast h1

theorem mem_of_sum_single_eq {ι X : Type*} [Fintype ι] [DecidableEq X]
    (W : ι → X) (S : Finset X) (e : X → ℕ)
    (h : ∑ i, Finsupp.single (W i) (1 : ℤ) = ∑ w ∈ S, Finsupp.single w (e w : ℤ)) (i : ι) : W i ∈ S := by
  classical
  by_contra hx
  have hc := card_filter_eq_of_sum_single_eq W S e h (W i)
  rw [if_neg hx, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
  exact hc (Finset.mem_univ i) rfl

theorem exists_eq_of_sum_single_eq {ι X : Type*} [Fintype ι] [DecidableEq X]
    (W : ι → X) (S : Finset X) (e : X → ℕ)
    (h : ∑ i, Finsupp.single (W i) (1 : ℤ) = ∑ w ∈ S, Finsupp.single w (e w : ℤ))
    (he : ∀ w ∈ S, 0 < e w) {x : X} (hx : x ∈ S) : ∃ i, W i = x := by
  classical
  have hc := card_filter_eq_of_sum_single_eq W S e h x
  rw [if_pos hx] at hc
  have hne : (Finset.univ.filter fun i => W i = x).Nonempty := by
    rw [← Finset.card_pos, hc]; exact he x hx
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

theorem prod_eq_prod_pow_of_sum_single_eq {ι X M : Type*} [Fintype ι] [DecidableEq X] [CommMonoid M]
    (W : ι → X) (S : Finset X) (e : X → ℕ)
    (h : ∑ i, Finsupp.single (W i) (1 : ℤ) = ∑ w ∈ S, Finsupp.single w (e w : ℤ)) (f : X → M) :
    ∏ i, f (W i) = ∏ w ∈ S, f w ^ e w := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := S) (g := W)
    (fun i _ => mem_of_sum_single_eq W S e h i) f]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.prod_const, card_filter_eq_of_sum_single_eq W S e h x, if_pos hx]

theorem phi_eq_mul {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (data : ModularCurve.ModularPolynomialData p) {R : Type*} [CommRing R] (φ : R →+* LaurentSeries L)
    (hφ : Function.Injective φ) (jR jp : R)
    (hjR : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; φ jR = ModularCurve.qExpand L p (ModularCurve.jqModC L))
    (hjp : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      φ jp = ModularCurve.qExpand L p (ModularCurve.qExpand L p (ModularCurve.jqModC L)))
    (E : Polynomial R)
    (hE : E.map φ = ∏ i : Fin p, (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ (i : ℕ)) (ModularCurve.jqModC L)))) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) jR) = (Polynomial.X - Polynomial.C jp) * E := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply Polynomial.map_injective φ hφ
  have hsplit := ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot (K := L) p ζ hζ data 1 1
  simp only [one_pow, ModularCurve.qTwist_one_apply, one_mul, ModularCurve.qExpand_one_apply] at hsplit
  have h1 : ModularCurve.qExpand L (p * 1) (ModularCurve.jqModC L) = φ jR := by
    rw [hjR]; exact ModularCurve.qExpand_congr (mul_one p) _
  have h2 : ModularCurve.qExpand L (p * (p * 1)) (ModularCurve.jqModC L) = φ jp := by
    rw [hjp, ModularCurve.qExpand_qExpand]; exact ModularCurve.qExpand_congr (by ring) _
  rw [h1, h2, Finset.prod_range (fun b => Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ b) (ModularCurve.jqModC L)))] at hsplit
  rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hE, Polynomial.map_map]
  have hcomp : φ.comp (Polynomial.eval₂RingHom (Int.castRingHom R) jR) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (φ jR) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [eq_intCast, map_intCast]
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hcomp, hsplit]

theorem vals_eq {Qb : Type*} [Field Qb] [IsAlgClosed Qb] (Pl : ValuationSubring Qb)
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (πk : ↥Pl →+* k)
    (data : ModularCurve.ModularPolynomialData p) {R : Type*} [CommRing R]
    (jR jp : R) (E : Polynomial R) (ψ : R →+* ↥Pl)
    (hΦ : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) jR) = (Polynomial.X - Polynomial.C jp) * E)
    (vals : Fin p → ↥Pl)
    (hE : E.map (Pl.subtype.comp ψ) = ∏ i : Fin p, (Polynomial.X - Polynomial.C ((vals i : ↥Pl) : Qb)))
    (hb : πk (ψ jp) ^ p = πk (ψ jR)) :
    (Finset.univ : Finset (Fin p)).val.map (fun i => πk (vals i)) =
      {πk (ψ jR) ^ p} + Multiset.replicate (p - 1) (πk (ψ jp)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let PPl : Polynomial ↥Pl := (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) jR)).map ψ
  have hmon : PPl.Monic := (data.monic.map _).map _

  have hred : PPl.map πk = (Polynomial.C (πk (ψ jR) ^ p) - Polynomial.X) * (Polynomial.C (πk (ψ jR)) - Polynomial.X ^ p) := by
    have hK := ModularCurve.modularPolynomial_kronecker p data
    let castk : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
    have hcomp : (πk.comp ψ).comp (Polynomial.eval₂RingHom (Int.castRingHom R) jR) =
        (Polynomial.eval₂RingHom castk (πk (ψ jR))).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp only [eq_intCast, map_intCast]
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_mapRingHom,
          Polynomial.map_X]
    change ((data.Φ.map _).map ψ).map πk = _
    rw [Polynomial.map_map, Polynomial.map_map, hcomp, ← Polynomial.map_map, hK]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.C_pow]

  let r : Qb → k := fun x => if h : x ∈ Pl then πk ⟨x, h⟩ else 0
  have hr : ∀ a : ↥Pl, r a = πk a := fun a => by
    simp only [r, dif_pos a.2, Subtype.coe_eta]
  have hKF := Polynomial.Monic.map_roots_eq_of_map_eq_kroneckerFibre (L := Qb) (A := Pl) (k := k) p πk r hr hmon
    (πk (ψ jR)) (πk (ψ jp)) hb hred
  have hmapQ : PPl.map (algebraMap ↥Pl Qb) = (Polynomial.X - Polynomial.C ((ψ jp : ↥Pl) : Qb)) *
      ∏ i : Fin p, (Polynomial.X - Polynomial.C ((vals i : ↥Pl) : Qb)) := by
    change ((data.Φ.map _).map ψ).map _ = _
    have hc' : (algebraMap ↥Pl Qb).comp ψ = Pl.subtype.comp ψ := RingHom.ext fun _ => rfl
    rw [Polynomial.map_map, hΦ, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc', hE]
    rfl
  have hne2 : (∏ i : Fin p, (Polynomial.X - Polynomial.C ((vals i : ↥Pl) : Qb))) ≠ 0 :=
    (Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _).ne_zero
  have hne1 : (Polynomial.X - Polynomial.C ((ψ jp : ↥Pl) : Qb)) *
      ∏ i : Fin p, (Polynomial.X - Polynomial.C ((vals i : ↥Pl) : Qb)) ≠ 0 :=
    ((Polynomial.monic_X_sub_C _).mul (Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _)).ne_zero
  rw [hmapQ, Polynomial.roots_mul hne1, Polynomial.roots_X_sub_C, Polynomial.roots_prod _ _ hne2] at hKF
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_add, Multiset.map_singleton,
    Multiset.map_map, Function.comp_def, hr] at hKF

  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.one_le).symm
  have hrep : p • ({πk (ψ jp)} : Multiset k) = {πk (ψ jp)} + Multiset.replicate (p - 1) (πk (ψ jp)) := by
    rw [Multiset.nsmul_singleton]
    conv_lhs => rw [hp1]
    rw [Multiset.replicate_succ, Multiset.singleton_add]
  rw [hrep, add_left_comm ({πk (ψ jR) ^ p} : Multiset k) {πk (ψ jp)} (Multiset.replicate (p - 1) (πk (ψ jp)))] at hKF
  exact add_left_cancel hKF

end SheetSort

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul.ModularCurve _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in
set_option maxHeartbeats 6400000 in

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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)

    (jp : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hjp : (((jp : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]

    (hdeg : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p) = p) :
    ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥Pl),

      ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = ρ →
      Spec.map (CommRingCat.ofHom (Pl.subtype.comp ψ)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j =
            (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →

      (πk.comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) = (πk.comp ψ) jp ^ p →
      (πk.comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) ^ (p ^ 2) ≠ (πk.comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) →
      ∃ (Qp : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) (ψp : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥Pl)
        (Q : Fin (p - 1) → AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) (ψQ : Fin (p - 1) → (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥Pl)),

        ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1) =
          Finsupp.single Qp 1 + ∑ i : Fin (p - 1), Finsupp.single (Q i) 1 ∧

        (ψp.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = ρ ∧
          Spec.map (CommRingCat.ofHom (Pl.subtype.comp ψp)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j =
            (Mη.pointEquivPlace.symm Qp).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          (πk.comp ψp) (ModularCurve.TwoChart.jChartFin A (↥K) j) = (πk.comp ψp) jp ^ p ∧
          (πk.comp ψp) (ModularCurve.TwoChart.jChartFin A (↥K) j) ^ (p ^ 2) ≠ (πk.comp ψp) (ModularCurve.TwoChart.jChartFin A (↥K) j)) ∧

        ∀ i : Fin (p - 1),
          (ψQ i).comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = ρ ∧
          Spec.map (CommRingCat.ofHom (Pl.subtype.comp (ψQ i))) ≫ ModularCurve.TwoChart.ιFin A (↥K) j =
            (Mη.pointEquivPlace.symm (Q i)).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          (πk.comp (ψQ i)) jp = (πk.comp (ψQ i)) (ModularCurve.TwoChart.jChartFin A (↥K) j) ^ p ∧
          (πk.comp (ψQ i)) (ModularCurve.TwoChart.jChartFin A (↥K) j) ^ (p ^ 2) ≠ (πk.comp (ψQ i)) (ModularCurve.TwoChart.jChartFin A (↥K) j)
 := by
  classical
  intro P ψ hψA hxP hC2 hFp2
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  let Qb := AlgebraicClosure ℚ
  let R := ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)
  let Fb := ↥(ModularCurve.x1FunctionFieldBar (M * p))
  let Ft := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))
  let α : Fb →ₐ[Qb] Ft := ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p
  let β : Fb →ₐ[Qb] Ft := ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p
  let ιF := ModularCurve.TwoChart.ιFin A (↥K) j
  let prQ := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))

  let U : Mη.C.Opens := (eη ≫ prQ) ⁻¹ᵁ (ιF ''ᵁ ⊤)
  let rd : R →+* Fb :=
    Mη.ffEquiv.symm.toRingHom.comp
      ((Mη.C.germToFunctionField U).hom.comp
        (((eη ≫ prQ).app (ιF ''ᵁ ⊤)).hom.comp
          ((ιF.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)))
  have hrd_coe : ∀ a : R, ((rd a : Fb) : LaurentSeries Qb) =
      ModularCurve.coeffMap (algebraMap L Qb) ((a : ↥K) : LaurentSeries L) := fun a => hMηpin a

  let ψ' : R →+* Qb := Pl.subtype.comp ψ

  haveI hCurve : IsCurveOver Qb Fb := ModularCurve.isCurveOver_x1FunctionFieldBar (M * p)
  have hratFb : ∀ v : Place Qb Fb, v.IsRational := fun v =>
    haveI := IsCurveOver.finiteResidue (K := Qb) v
    Place.sheetSort_isRational_of_finite v

  have hfinβ : FiniteAlong Qb β := by
    letI := algebraAlong β
    change Module.Finite Fb Ft
    apply Module.finite_of_finrank_pos
    change 0 < finrankAlong Qb β
    rw [hdeg]; exact hp.pos
  have hsepβ : SeparableAlong Qb β := separableAlong_of_charZero _ hβ
  have hFIβ : FundamentalIdentityAlong Qb β hβ := fundamentalIdentityAlong _ hβ hfinβ hsepβ
  have hfinFt : ∀ w : Place Qb Ft, Module.Finite Qb w.ResidueField := by
    intro w
    letI := algebraAlong β
    haveI := isScalarTower_along β
    haveI : Module.Finite Fb Ft := hfinβ
    exact Place.sheetSort_finite_residueField_of_isCurveOver (K := Qb) Fb w
  have hdeg1 : ∀ w : Place Qb Ft, w.deg = 1 := fun w =>
    haveI := hfinFt w
    w.deg_eq_one_of_isAlgClosed_of_finite
  have hratFt : ∀ w : Place Qb Ft, w.IsRational := fun w =>
    haveI := hfinFt w
    Place.sheetSort_isRational_of_finite w
  obtain ⟨W, hW, hWP⟩ := Divisor.exists_pullbackAlong_single_one_eq_sum β hβ hFIβ P
    (IsCurveOver.deg_eq_one_of_isAlgClosed P) (fun w _ => hdeg1 w) p hdeg

  let Q : Fin p → Place Qb Fb := fun i => (W i).restrictAlong α hα
  have hdiv : ModularCurve.heckeDivOneBar (L := Qb) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1) =
      ∑ i : Fin p, Finsupp.single (Q i) 1 := by
    change Divisor.correspondence β α hβ hα (Finsupp.single P 1) = _
    rw [Divisor.correspondence_apply, hW, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Divisor.pushforwardAlong_single_one α hα (W i) (hdeg1 (W i))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)

  have hK5 := ModularCurve.XOneP.mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
    p M L K A j Mη eη heη
  have hvalP : ∀ r : R, rd r ∈ P.toValuationSubring ∧ P.evalAt (rd r) = ψ' r := by
    intro r
    have h := hK5.1 (Mη.pointEquivPlace.symm P) ψ' hxP.symm r
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hrd_const : ∀ a : A, rd (algebraMap A R a) = algebraMap Qb Fb (algebraMap A Qb a) := fun a => hK5.2.2 a

  let jR : R := ModularCurve.TwoChart.jChartFin A (↥K) j
  have hjP : rd jR ∈ P.toValuationSubring := (hvalP jR).1
  have hjRcoe : ((jR : ↥K) : LaurentSeries L) = (j : LaurentSeries L) := rfl
  have hjL : (j : LaurentSeries L) = ModularCurve.jqModC L := by
    rw [hj, ModularCurve.coeffEmb, ← ModularCurve.jqModC_rat]
    exact ModularCurve.map_jqModC (algebraMap ℚ L)
  have hjcoe : ((rd jR : Fb) : LaurentSeries Qb) = ModularCurve.jqModC Qb := by
    rw [hrd_coe, hjRcoe, hjL]
    exact ModularCurve.map_jqModC (algebraMap L Qb)
  have hβjcoe : ((β (rd jR) : Ft) : LaurentSeries Qb) = ModularCurve.qExpand Qb p (ModularCurve.jqModC Qb) := by
    rw [ModularCurve.coe_heckeBetaOneBar _ _ hβdef, hjcoe]
  have hαjcoe : ((α (rd jR) : Ft) : LaurentSeries Qb) = ModularCurve.jqModC Qb := by
    rw [ModularCurve.coe_heckeAlphaOneBar, hjcoe]

  have hregW : ∀ w : Place Qb Ft, w.restrictAlong β hβ = P → ∀ r : R, α (rd r) ∈ w.toValuationSubring := by
    intro w hw r
    have hβj : β (rd jR) ∈ w.toValuationSubring := by
      rw [← Place.sheetSort_mem_restrictAlong_iff β hβ w, hw]; exact hjP
    have hαj : α (rd jR) ∈ w.toValuationSubring :=
      ModularCurve.mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem Qb p _ w (α (rd jR)) (β (rd jR)) hαjcoe hβjcoe hβj

    have hint : IsIntegral (Algebra.adjoin A ({j} : Set ↥K)) (r : ↥K) := r.2
    have hle : Algebra.adjoin A ({j} : Set ↥K) ≤ ModularCurve.TwoChart.chartAlgFin A (↥K) j :=
      ModularCurve.TwoChart.adjoin_le_chartAlg A (↥K) {j}
    let incl : ↥(Algebra.adjoin A ({j} : Set ↥K)) →+* R := (Subalgebra.inclusion hle).toRingHom
    let θ : R →+* Ft := (α : Fb →ₐ[Qb] Ft).toRingHom.comp rd
    have hgen_mem : ∀ (x : ↥K) (hx : x ∈ Algebra.adjoin A ({j} : Set ↥K)), θ (incl ⟨x, hx⟩) ∈ w.toValuationSubring := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hαj
      | algebraMap a =>
        have h1 : incl ⟨algebraMap A (↥K) a, Subalgebra.algebraMap_mem _ a⟩ = algebraMap A R a := rfl
        change α (rd (incl ⟨algebraMap A (↥K) a, _⟩)) ∈ _
        rw [h1, hrd_const, AlgHom.commutes]
        exact w.algebraMap_mem' _
      | add x y hx hy ihx ihy =>
        have : incl ⟨x + y, Subalgebra.add_mem _ hx hy⟩ = incl ⟨x, hx⟩ + incl ⟨y, hy⟩ := rfl
        rw [this, map_add]; exact add_mem ihx ihy
      | mul x y hx hy ihx ihy =>
        have : incl ⟨x * y, Subalgebra.mul_mem _ hx hy⟩ = incl ⟨x, hx⟩ * incl ⟨y, hy⟩ := rfl
        rw [this, map_mul]; exact mul_mem ihx ihy
    let ρw : ↥(Algebra.adjoin A ({j} : Set ↥K)) →+* ↥(w.toValuationSubring) :=
      (θ.comp incl).codRestrict w.toValuationSubring.toSubring (fun x => hgen_mem x.1 x.2)
    obtain ⟨Pm, hPm, hPr⟩ := hint
    have hθr : IsIntegral ↥(w.toValuationSubring) (θ r) := by
      refine ⟨Pm.map ρw, hPm.map ρw, ?_⟩
      rw [Polynomial.eval₂_map]
      have h1 : (algebraMap ↥(w.toValuationSubring) Ft).comp ρw = θ.comp incl := RingHom.ext fun x => rfl
      have h2 : Polynomial.eval₂ incl r Pm = 0 := by
        apply Subtype.val_injective
        have h3 := Polynomial.hom_eval₂ Pm incl (algebraMap R ↥K) r
        have h4 : (algebraMap R ↥K).comp incl = algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K)) ↥K := RingHom.ext fun x => rfl
        rw [h4] at h3
        exact h3.trans hPr
      rw [h1, ← Polynomial.hom_eval₂, h2, map_zero]
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(w.toValuationSubring)) (K := Ft)).mp hθr
    change θ r ∈ w.toValuationSubring
    rw [← hz]; exact z.2
  have hregQ : ∀ (i : Fin p) (r : R), rd r ∈ (Q i).toValuationSubring := by
    intro i r
    rw [Place.sheetSort_mem_restrictAlong_iff α hα (W i)]
    exact hregW (W i) (hWP i) r

  have hψex : ∀ i : Fin p, ∃ ψi : R →+* Qb, (∀ r, ψi r = (Q i).evalAt (rd r)) := by
    intro i
    refine ⟨{ toFun := fun r => (Q i).evalAt (rd r), map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
      fun r => rfl⟩
    · simp only [map_one, Place.evalAt_one]
    · intro a b; simp only [map_mul]; exact Place.evalAt_mul_of_mem _ (hratFb _) (hregQ i a) (hregQ i b)
    · simp only [map_zero]; exact Place.sheetSort_evalAt_zero _
    · intro a b; simp only [map_add]; exact Place.sheetSort_evalAt_add _ (hratFb _) (hregQ i a) (hregQ i b)
  choose ψv hψv using hψex
  have hψvA : ∀ (i : Fin p) (a : A), ψv i (algebraMap A R a) = algebraMap A Qb a := by
    intro i a
    rw [hψv, hrd_const, Place.evalAt_algebraMap_eq]

  have hWval : ∀ (i : Fin p) (g : R), (W i).evalAt (α (rd g)) = ψv i g := by
    intro i g
    rw [hψv, Place.sheetSort_evalAt_restrictAlong α hα (W i) (hratFb _) (hregQ i g)]

  have hζ0 : (ζ : L) ≠ 0 := hζ.ne_zero hp.ne_zero
  let ζu : Lˣ := Units.mk0 ζ hζ0
  have hζu : IsPrimitiveRoot (ζu : L) p := hζ
  have hdegL : AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L (M * p) p) = p := by
    rw [ModularCurve.finrankAlong_heckeBetaOneBar L (M * p) p hβdef, if_pos (dvd_mul_left p M)]
  let ζb : Qbˣ := Units.map (algebraMap L Qb : L →* Qb) ζu
  have hζb : IsPrimitiveRoot (ζb : Qb) p := by
    have : (ζb : Qb) = algebraMap L Qb ζ := rfl
    rw [this]; exact hζ.map_of_injective (algebraMap L Qb).injective
  have hFj : ModularCurve.jqModC Qb ∈ ModularCurve.laurentBaseChange Qb (ModularCurve.x1FunctionField (M * p)) := by
    rw [← hjcoe]; exact (rd jR).2

  let φL : R →+* LaurentSeries L := (ModularCurve.qExpand L p).comp
    ((algebraMap ↥K (LaurentSeries L)).comp (algebraMap R ↥K))
  have hφL : ∀ r : R, φL r = ModularCurve.qExpand L p ((r : ↥K) : LaurentSeries L) := fun r => rfl
  have hφLinj : Function.Injective φL := by
    intro a b h
    rw [hφL, hφL] at h
    exact Subtype.val_injective (Subtype.val_injective (ModularCurve.qExpand_injective (R := L) (N := p) h))
  haveI : Infinite Qb := Infinite.of_injective _ Nat.cast_injective

  have hV : ∀ g : R, ∃ E : Polynomial R, E.Monic ∧ E.natDegree = p ∧
      E.map φL = ∏ i' : Fin p, (Polynomial.X - Polynomial.C
        (ModularCurve.qTwist (ζu ^ (i' : ℕ)) (((g : R) : ↥K) : LaurentSeries L))) ∧
      E.map ψ' = ∏ i : Fin p, (Polynomial.X - Polynomial.C (ψv i g)) := by
    intro g
    letI instβ : Algebra Fb Ft := algebraAlong β
    haveI := isScalarTower_along β
    haveI : Module.Finite Fb Ft := hfinβ
    haveI : Algebra.IsSeparable Fb Ft := hsepβ
    haveI := isIntegral_along β hβ
    obtain ⟨E, hEmon, hEdeg, hEmap, -, -⟩ :=
      ModularCurve.XOneP.exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul
        p M L ζu hζu K hK A hAp hζA j hj hβdef hdegL g
    refine ⟨E, hEmon, hEdeg, hEmap, ?_⟩
    have hEdeg' : E.natDegree = p := hEdeg

    have hWfib : ∑ i : Fin p, Finsupp.single (W i) (1 : ℤ) =
        ∑ w ∈ P.fiber Ft, Finsupp.single w ((w.ramificationIndex Fb : ℕ) : ℤ) := by
      rw [← hW]
      have h := Divisor.pullbackAlong_single β hβ P 1
      rw [h]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [one_mul]
      rfl
    have hfibW : ∀ w ∈ P.fiber Ft, w.restrictAlong β hβ = P := fun w hw => Place.mem_fiber.mp hw

    have key : ∀ c : Qb, (∀ i : Fin p, ψv i g ≠ c) →
        (E.map ψ').eval c = ∏ i : Fin p, (c - ψv i g) := by
      intro c hc

      have hcFt : ((algebraMap Qb Ft c : Ft) : LaurentSeries Qb) = HahnSeries.C c := by
        change algebraMap Qb (LaurentSeries Qb) c = _
        rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
      have hcFb : ∀ n : ℕ, (((algebraMap Qb Fb c ^ n : Fb)) : LaurentSeries Qb) = HahnSeries.C c ^ n := fun n => by
        rw [IntermediateField.coe_pow]
        refine congrArg (· ^ n) ?_
        change algebraMap Qb (LaurentSeries Qb) c = _
        rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
      let y : Ft := α (rd g) - algebraMap Qb Ft c
      have hymem : ∀ w : Place Qb Ft, w.restrictAlong β hβ = P → y ∈ w.toValuationSubring :=
        fun w hw => sub_mem (hregW w hw g) (w.algebraMap_mem' c)
      have hyval : ∀ w : Place Qb Ft, w.restrictAlong β hβ = P → w.evalAt y = w.evalAt (α (rd g)) - c := by
        intro w hw
        have h2 : y = α (rd g) + algebraMap Qb Ft (-c) := by rw [map_neg, ← sub_eq_add_neg]
        rw [h2, Place.sheetSort_evalAt_add _ (hratFt _) (hregW _ hw g) (w.algebraMap_mem' _),
          Place.evalAt_algebraMap_eq, ← sub_eq_add_neg]
      have hyWi : ∀ i : Fin p, (W i).evalAt y = ψv i g - c := fun i => by rw [hyval _ (hWP i), hWval]
      have hy0 : y ≠ 0 := by
        intro h0
        have h := hyWi ⟨0, hp.pos⟩
        rw [h0, Place.sheetSort_evalAt_zero] at h
        exact hc _ (sub_eq_zero.mp h.symm)

      have hK1a := ModularCurve.coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq Qb (M * p) p hFj hβdef hdeg ζb hζb y

      have hycoe : (y : LaurentSeries Qb) =
          ModularCurve.coeffMap (algebraMap L Qb) ((g : ↥K) : LaurentSeries L) - HahnSeries.C c := by
        change ((α (rd g) : Ft) : LaurentSeries Qb) - ((algebraMap Qb Ft c : Ft) : LaurentSeries Qb) = _
        rw [ModularCurve.coe_heckeAlphaOneBar, hrd_coe, hcFt]
      have htw : ∀ i' : Fin p, ModularCurve.qTwist (ζb ^ (i' : ℕ)) (y : LaurentSeries Qb) =
          ModularCurve.coeffMap (algebraMap L Qb) (ModularCurve.qTwist (ζu ^ (i' : ℕ)) ((g : ↥K) : LaurentSeries L))
            - HahnSeries.C c := by
        intro i'
        rw [hycoe, map_sub, ModularCurve.sheetSort_qTwist_C, ModularCurve.sheetSort_coeffMap_qTwist, map_pow]

      let σ : LaurentSeries L →+* LaurentSeries Qb := ModularCurve.coeffMap (algebraMap L Qb)
      have hEmap' : (E.map (σ.comp φL)) = ∏ i' : Fin p, (Polynomial.X - Polynomial.C
          (σ (ModularCurve.qTwist (ζu ^ (i' : ℕ)) ((g : ↥K) : LaurentSeries L)))) := by
        rw [← Polynomial.map_map, hEmap, Polynomial.map_prod]
        refine Finset.prod_congr rfl fun i' _ => ?_
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

      have heval_prod : (E.map (σ.comp φL)).eval (HahnSeries.C c) =
          (-1) ^ p * ∏ i' : Fin p, ModularCurve.qTwist (ζb ^ (i' : ℕ)) (y : LaurentSeries Qb) := by
        rw [hEmap', Polynomial.eval_prod]
        have : ∀ i' ∈ (Finset.univ : Finset (Fin p)), Polynomial.eval (HahnSeries.C c)
            (Polynomial.X - Polynomial.C (σ (ModularCurve.qTwist (ζu ^ (i' : ℕ)) ((g : ↥K) : LaurentSeries L)))) =
            (-1) * ModularCurve.qTwist (ζb ^ (i' : ℕ)) (y : LaurentSeries Qb) := by
          intro i' _
          rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, htw, neg_one_mul, neg_sub]
        rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

      let rs : Fb := ∑ n ∈ Finset.range (p + 1), algebraMap Qb Fb c ^ n * rd (E.coeff n)
      have hσφ : ∀ r : R, σ (φL r) = ModularCurve.qExpand Qb p ((rd r : Fb) : LaurentSeries Qb) := by
        intro r
        change ModularCurve.coeffMap (algebraMap L Qb) (ModularCurve.qExpand L p (((r : ↥K)) : LaurentSeries L)) = _
        rw [ModularCurve.sheetSort_coeffMap_qExpand, hrd_coe]
      have heval_sum : (E.map (σ.comp φL)).eval (HahnSeries.C c) =
          ModularCurve.qExpand Qb p ((rs : Fb) : LaurentSeries Qb) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, hEdeg']
        have hcoe : ((rs : Fb) : LaurentSeries Qb) = ∑ n ∈ Finset.range (p + 1),
            (HahnSeries.C c) ^ n * ((rd (E.coeff n) : Fb) : LaurentSeries Qb) := by
          change (ModularCurve.x1FunctionFieldBar (M * p)).val rs = _
          rw [map_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [map_mul]
          exact congrArg (· * _) (hcFb n)
        rw [hcoe, map_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [RingHom.comp_apply, hσφ, map_mul, map_pow, ModularCurve.qExpand_C, mul_comm]

      have hnorm : (Algebra.norm Fb y : Fb) = (-1) ^ p * rs := by
        apply Subtype.val_injective
        apply ModularCurve.qExpand_injective (R := Qb) (N := p)
        have h1 : ModularCurve.qExpand Qb p ((Algebra.norm Fb y : Fb) : LaurentSeries Qb) =
            ∏ i' : Fin p, ModularCurve.qTwist (ζb ^ (i' : ℕ)) (y : LaurentSeries Qb) := by
          rw [← ModularCurve.coe_heckeBetaOneBar _ _ hβdef]; exact hK1a
        have h2 : ∏ i' : Fin p, ModularCurve.qTwist (ζb ^ (i' : ℕ)) (y : LaurentSeries Qb) =
            (-1) ^ p * ModularCurve.qExpand Qb p ((rs : Fb) : LaurentSeries Qb) := by
          have h := heval_prod.symm.trans heval_sum
          rw [← h, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
        rw [h1, h2]
        change _ = ModularCurve.qExpand Qb p ((((-1 : Fb) ^ p * rs : Fb)) : LaurentSeries Qb)
        rw [IntermediateField.coe_mul, IntermediateField.coe_pow, map_mul, map_pow]
        congr 1
        rw [IntermediateField.coe_neg, IntermediateField.coe_one, map_neg, map_one]

      have hrs_terms : ∀ n ∈ Finset.range (p + 1), algebraMap Qb Fb c ^ n * rd (E.coeff n) ∈ P.toValuationSubring :=
        fun n _ => mul_mem (pow_mem (P.algebraMap_mem' c) n) (hvalP (E.coeff n)).1
      have hrs_mem : rs ∈ P.toValuationSubring := Subring.sum_mem _ hrs_terms
      have hrs_eval : P.evalAt rs = (E.map ψ').eval c := by
        rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, hEdeg',
          Place.sheetSort_evalAt_sum P (hratFb P) _ _ hrs_terms]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Place.evalAt_mul_of_mem P (hratFb P) (pow_mem (P.algebraMap_mem' c) n) (hvalP _).1, (hvalP (E.coeff n)).2,
          ← map_pow, Place.evalAt_algebraMap_eq, mul_comm]
      have hnegp : ((-1 : Fb) ^ p) = algebraMap Qb Fb ((-1) ^ p) := by rw [map_pow, map_neg, map_one]
      have hnmem : (Algebra.norm Fb y : Fb) ∈ P.toValuationSubring := by
        rw [hnorm, hnegp]; exact mul_mem (P.algebraMap_mem' _) hrs_mem
      have hrs_norm : rs = algebraMap Qb Fb ((-1) ^ p) * (Algebra.norm Fb y : Fb) := by
        rw [hnorm, ← hnegp, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

      have hord : ∀ w ∈ P.fiber Ft, w.ord y = 0 := by
        intro w hw
        obtain ⟨i, rfl⟩ := SheetSort.exists_eq_of_sum_single_eq W (P.fiber Ft) (fun w => w.ramificationIndex Fb) hWfib
          (fun w _ => w.ramificationIndex_pos (F := Fb)) hw
        refine Place.sheetSort_ord_eq_zero_of_evalAt_ne_zero _ (hymem _ (hWP i)) ?_
        rw [hyWi]
        exact sub_ne_zero.mpr (hc i)
      have hVN := Place.evalAt_norm_eq_prod_fiber (K := Qb) (F := Fb) (F' := Ft) P y hy0 (hratFb P)
        (fun w _ => hratFt w) hord
      have hprod : ∏ w ∈ P.fiber Ft, w.evalAt y ^ w.ramificationIndex Fb = ∏ i : Fin p, (W i).evalAt y :=
        (SheetSort.prod_eq_prod_pow_of_sum_single_eq W (P.fiber Ft) (fun w => w.ramificationIndex Fb) hWfib
          (fun w => w.evalAt y)).symm
      calc (E.map ψ').eval c = P.evalAt rs := hrs_eval.symm
        _ = (-1) ^ p * P.evalAt (Algebra.norm Fb y : Fb) := by
            rw [hrs_norm, Place.evalAt_mul_of_mem P (hratFb P) (P.algebraMap_mem' _) hnmem, Place.evalAt_algebraMap_eq]
        _ = (-1) ^ p * ∏ i : Fin p, (ψv i g - c) := by
            rw [hVN, hprod]
            exact congrArg _ (Finset.prod_congr rfl fun i _ => hyWi i)
        _ = ∏ i : Fin p, (c - ψv i g) := by
            have : ∀ i ∈ (Finset.univ : Finset (Fin p)), (c - ψv i g) = (-1) * (ψv i g - c) := by
              intro i _; ring
            rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin]

    apply Polynomial.eq_of_infinite_eval_eq
    have hfin : (Set.range fun i : Fin p => ψv i g).Finite := Set.finite_range _
    refine hfin.infinite_compl.mono ?_
    intro c hc
    have hc' : ∀ i : Fin p, ψv i g ≠ c := fun i h => hc ⟨i, h⟩
    simp only [Set.mem_setOf_eq]
    rw [key c hc', Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

  have hψPl : ∀ (i : Fin p) (g : R), ψv i g ∈ Pl := by
    intro i g
    obtain ⟨E, hEmon, -, -, hEψ⟩ := hV g
    have hroot : (E.map ψ').eval (ψv i g) = 0 := by
      rw [hEψ, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hint : IsIntegral ↥Pl (ψv i g) := by
      refine ⟨E.map ψ, hEmon.map ψ, ?_⟩
      rw [← Polynomial.eval_map, Polynomial.map_map]
      exact hroot
    obtain ⟨c', hc'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Pl) (K := Qb)).mp hint
    rw [← hc']; exact c'.2
  let ψPl : Fin p → (R →+* ↥Pl) := fun i => (ψv i).codRestrict Pl.toSubring (hψPl i)
  have hψPl_val : ∀ (i : Fin p) (r : R), ((ψPl i r : ↥Pl) : Qb) = ψv i r := fun i r => rfl
  have hψPlA : ∀ i : Fin p, (ψPl i).comp (algebraMap A R) = ρ := by
    intro i; ext a
    change ψv i (algebraMap A R a) = ((ρ a : ↥Pl) : Qb)
    rw [hψvA]
    exact (congrArg (fun f : A →+* Qb => f a) hρ).symm

  have hpt : ∀ i : Fin p, Spec.map (CommRingCat.ofHom (Pl.subtype.comp (ψPl i))) ≫ ιF =
      (Mη.pointEquivPlace.symm (Q i)).1 ≫ eη ≫ prQ := by
    intro i
    obtain ⟨ψQ, hψQ⟩ := ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
      p M L K A j Mη eη heη (Mη.pointEquivPlace.symm (Q i)) (by rw [Equiv.apply_symm_apply]; exact hregQ i jR)
    have hψQ_eq : ψQ = Pl.subtype.comp (ψPl i) := by
      ext r
      have h := (hK5.1 (Mη.pointEquivPlace.symm (Q i)) ψQ hψQ r).2
      rw [Equiv.apply_symm_apply] at h
      rw [← h]
      change (Q i).evalAt (rd r) = ψv i r
      exact (hψv i r).symm
    rw [← hψQ_eq]; exact hψQ.symm

  have hαjp : α (rd jp) = β (rd jR) := by
    apply Subtype.val_injective
    change ((α (rd jp) : Ft) : LaurentSeries Qb) = ((β (rd jR) : Ft) : LaurentSeries Qb)
    rw [ModularCurve.coe_heckeAlphaOneBar, hrd_coe, hjp, ModularCurve.coe_heckeBetaOneBar _ _ hβdef, hrd_coe, hjRcoe,
      hj, ModularCurve.coeffEmb, ModularCurve.sheetSort_coeffMap_qExpand, ModularCurve.sheetSort_coeffMap_qExpand]
  have hjpval : ∀ i : Fin p, ψv i jp = ψ' jR := by
    intro i
    rw [← hWval, hαjp, Place.sheetSort_evalAt_restrictAlong β hβ (W i) (g := rd jR) (by rw [hWP i]; exact hratFb P)
      (by rw [hWP i]; exact hjP), hWP i]
    exact (hvalP jR).2
  have hχjp : ∀ i : Fin p, πk (ψPl i jp) = πk (ψ jR) := by
    intro i
    congr 1
    exact Subtype.ext (hjpval i)

  obtain ⟨Ej, hEjmon, hEjdeg, hEjmap, hEjψ⟩ := hV jR
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  have hφjR : φL jR = ModularCurve.qExpand L p (ModularCurve.jqModC L) := by rw [hφL, hjRcoe, hjL]
  have hφjp : φL jp = ModularCurve.qExpand L p (ModularCurve.qExpand L p (ModularCurve.jqModC L)) := by
    rw [hφL, hjp, ← hjL, hj, ModularCurve.coeffEmb, ModularCurve.sheetSort_coeffMap_qExpand]
  have hEjmap' : Ej.map φL = ∏ i : Fin p, (Polynomial.X - Polynomial.C
      (ModularCurve.qTwist (ζu ^ (i : ℕ)) (ModularCurve.jqModC L))) := by
    rw [hEjmap]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hjRcoe, hjL]
  have hΦ := SheetSort.phi_eq_mul p ζu hζu data φL hφLinj jR jp hφjR hφjp Ej hEjmap'
  have hb : πk (ψ jp) ^ p = πk (ψ jR) := hC2.symm
  have hvals := SheetSort.vals_eq Pl p πk data jR jp Ej ψ hΦ (fun i => ψPl i jR) hEjψ hb

  have hab : πk (ψ jR) ^ p ≠ πk (ψ jp) := by
    intro h
    apply hFp2
    change πk (ψ jR) ^ (p ^ 2) = πk (ψ jR)
    rw [sq, pow_mul, h, hb]
  have hmemv : ∀ i : Fin p, πk (ψPl i jR) = πk (ψ jR) ^ p ∨ πk (ψPl i jR) = πk (ψ jp) := by
    intro i
    have h : πk (ψPl i jR) ∈ (Finset.univ : Finset (Fin p)).val.map (fun i => πk (ψPl i jR)) :=
      Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    rw [hvals, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate] at h
    rcases h with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hex : ∃ i0 : Fin p, πk (ψPl i0 jR) = πk (ψ jR) ^ p := by
    have h : πk (ψ jR) ^ p ∈ (Finset.univ : Finset (Fin p)).val.map (fun i => πk (ψPl i jR)) := by
      rw [hvals]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))
    obtain ⟨i0, -, h0⟩ := Multiset.mem_map.mp h
    exact ⟨i0, h0⟩
  obtain ⟨i0, hi0⟩ := hex
  have huniq : ∀ i : Fin p, πk (ψPl i jR) = πk (ψ jR) ^ p → i = i0 := by
    intro i hi
    have hcnt : Multiset.count (πk (ψ jR) ^ p) ((Finset.univ : Finset (Fin p)).val.map (fun i => πk (ψPl i jR))) = 1 := by
      rw [hvals, Multiset.count_add, Multiset.count_singleton_self, Multiset.count_replicate, if_neg (Ne.symm hab)]
    rw [Multiset.count_map, Multiset.card_eq_one] at hcnt
    obtain ⟨i1, hi1⟩ := hcnt
    have h1 : i ∈ ({i1} : Multiset (Fin p)) := hi1 ▸ Multiset.mem_filter.mpr ⟨Finset.mem_univ_val i, hi.symm⟩
    have h0 : i0 ∈ ({i1} : Multiset (Fin p)) := hi1 ▸ Multiset.mem_filter.mpr ⟨Finset.mem_univ_val i0, hi0.symm⟩
    rw [Multiset.mem_singleton] at h1 h0
    rw [h1, h0]
  have hother : ∀ i : Fin p, i ≠ i0 → πk (ψPl i jR) = πk (ψ jp) := fun i hi =>
    (hmemv i).resolve_left fun h => hi (huniq i h)

  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  let e : Fin (p - 1 + 1) ≃ Fin p := finCongr hp1
  let x0 : Fin (p - 1 + 1) := e.symm i0
  let emb : Fin (p - 1) → Fin p := fun t => e (x0.succAbove t)
  have hemb : ∀ t, emb t ≠ i0 := by
    intro t h
    apply Fin.succAbove_ne x0 t
    apply e.injective
    rw [show e x0 = i0 from e.apply_symm_apply i0]
    exact h
  have hsum : ∀ f : Fin p → Divisor Qb Fb, ∑ i, f i = f i0 + ∑ t, f (emb t) := by
    intro f
    rw [← Equiv.sum_comp e f, Fin.sum_univ_succAbove (fun i => f (e i)) x0]
    simp only [emb, x0, Equiv.apply_symm_apply]

  have hFrob1 : (πk (ψ jR) ^ p) ^ (p ^ 2) ≠ πk (ψ jR) ^ p := by
    intro h
    apply hFp2
    change πk (ψ jR) ^ (p ^ 2) = πk (ψ jR)
    apply frobenius_inj k p
    rw [frobenius_def, frobenius_def, ← pow_mul, mul_comm, pow_mul]
    exact h
  have hFrob2 : πk (ψ jp) ^ (p ^ 2) ≠ πk (ψ jp) := by
    intro h
    apply hFp2
    change πk (ψ jR) ^ (p ^ 2) = πk (ψ jR)
    rw [← hb, ← pow_mul, mul_comm, pow_mul, h]

  refine ⟨Q i0, ψPl i0, fun t => Q (emb t), fun t => ψPl (emb t), ?_, ⟨hψPlA i0, hpt i0, ?_, ?_⟩, fun t => ?_⟩
  · rw [hdiv]; exact hsum _
  · change πk (ψPl i0 jR) = πk (ψPl i0 jp) ^ p
    rw [hχjp, hi0]
  · change πk (ψPl i0 jR) ^ (p ^ 2) ≠ πk (ψPl i0 jR)
    rw [hi0]; exact hFrob1
  · refine ⟨hψPlA _, hpt _, ?_, ?_⟩
    · change πk (ψPl (emb t) jp) = πk (ψPl (emb t) jR) ^ p
      rw [hχjp, hother _ (hemb t), hb]
    · change πk (ψPl (emb t) jR) ^ (p ^ 2) ≠ πk (ψPl (emb t) jR)
      rw [hother _ (hemb t)]; exact hFrob2

end

end S_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul (solution)
