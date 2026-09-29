-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/76f997c9-1a39-5a1f-9440-9958612b2679

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_tensor_chartAlgFin_of_charZero
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_exists_mul_mem_adjoin_jFull_jqN
import Theorems.Thm_ModularCurve_IgusaScheme_jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
p2m_attr_erase "instance" "IsLocalRing.instModuleResidueFieldOfAlgebra"

open scoped TensorProduct
p2m_open "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jq jqN jqN_mem modularFunctionFieldFull modularFunctionField_le_full qExpFunctionFieldC algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull"
namespace ChartBCAux
p2m_open "ModularCurve"

theorem eq_zero_of_sum_single_mul_coeffEmb_eq_zero (L : Type) [Field L] [CharZero L]
    {ι : Type} (s : Finset ι) (a : ι → L) (ha : LinearIndependent ℚ a)
    (f : ι → LaurentSeries ℚ) (h : ∑ i ∈ s, HahnSeries.single 0 (a i) * coeffEmb L (f i) = 0) :
    ∀ i ∈ s, f i = 0 := by
  intro i hi
  ext k
  have hk : (∑ i ∈ s, HahnSeries.single 0 (a i) * coeffEmb L (f i)).coeff k = 0 := by rw [h]; rfl
  rw [HahnSeries.coeff_sum] at hk
  simp only [HahnSeries.coeff_single_zero_mul, coeffEmb_coeff] at hk
  have hk' : ∑ j ∈ s, ((f j).coeff k) • a j = 0 := by
    rw [← hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have := linearIndependent_iff'.mp ha s (fun j => (f j).coeff k) hk' i hi
  simpa using this

theorem isLocalization_away_of_irreducible (A K : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] {ϖ : A}
    (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (pow_ne_zero _ hϖ.ne_zero))
  · intro z
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
    refine ⟨(a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩), ?_⟩
    have hsK : algebraMap A K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hs0
    change algebraMap A K a / algebraMap A K s * algebraMap A K (ϖ ^ n) = algebraMap A K (a * ↑u⁻¹)
    rw [div_mul_eq_mul_div, div_eq_iff hsK, ← map_mul, ← map_mul, hu]
    congr 1
    rw [mul_assoc, Units.inv_mul_cancel_left]
  · intro x y h
    exact ⟨1, by rw [IsFractionRing.injective A K h]⟩

theorem finite_quotient_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime]
    (I : Ideal ↥(GaloisRep.ratLocalizedAt p)) [CharP (↥(GaloisRep.ratLocalizedAt p) ⧸ I) p] :
    Finite (↥(GaloisRep.ratLocalizedAt p) ⧸ I) := by
  let φ : ZMod p →+* ↥(GaloisRep.ratLocalizedAt p) ⧸ I := ZMod.castHom (dvd_refl p) _
  refine Finite.of_surjective φ fun y => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hden : ¬ p ∣ (r : ℚ).den := (Nat.Prime.coprime_iff_not_dvd hp.out).mp r.2.symm
  have h1 : r * (((r : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) =
      (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) := by
    apply Subtype.ext
    change (r : ℚ) * ((((r : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) =
      ((((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
    simp [Rat.mul_den_eq_num]
  have hdenZ : (((r : ℚ).den : ℕ) : ZMod p) ≠ 0 := fun h =>
    hden ((CharP.cast_eq_zero_iff (ZMod p) p _).mp h)
  have hu : IsUnit ((((r : ℚ).den : ℕ)) : ↥(GaloisRep.ratLocalizedAt p) ⧸ I) := by
    rw [← map_natCast φ]
    exact (isUnit_iff_ne_zero.mpr hdenZ).map φ
  refine ⟨(((r : ℚ).num : ℤ) : ZMod p) * ((((r : ℚ).den : ℕ) : ZMod p))⁻¹, ?_⟩
  have e1 : Ideal.Quotient.mk I r * (((r : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt p) ⧸ I) =
      (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt p) ⧸ I) := by
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_mul, h1, map_intCast]
  have e2 : φ ((((r : ℚ).num : ℤ) : ZMod p) * ((((r : ℚ).den : ℕ) : ZMod p))⁻¹) *
      (((r : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt p) ⧸ I) =
      (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt p) ⧸ I) := by
    rw [← map_natCast φ, ← map_mul, mul_assoc, inv_mul_cancel₀ hdenZ, mul_one, map_intCast]
  exact (IsUnit.mul_left_inj hu).mp (e2.trans e1.symm)

end ModularCurve.ChartBCAux

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jq jqN jqN_mem modularFunctionFieldFull modularFunctionField_le_full qExpFunctionFieldC algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull"
namespace ChartBCAux
p2m_open "ModularCurve"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem injective_lift_coeffEmb (p : ℕ) [hp : Fact p.Prime]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥F₀]
    (B : Subalgebra ↥(GaloisRep.ratLocalizedAt p) ↥F₀)
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (K' : IntermediateField L (LaurentSeries L)) [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥K'] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) L ↥K']
    (g : ↥B →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥K')
    (hg : ∀ b : ↥B, algebraMap ↥K' (LaurentSeries L) (g b) = coeffEmb L (((b : ↥F₀)) : LaurentSeries ℚ)) :
    Function.Injective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) L ↥K') g
      (fun _ _ => Commute.all _ _)) := by
  classical
  have hpp : p.Prime := hp.out
  haveI hRdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hpp
  haveI hRfrac : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hpirr : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := GaloisRep.irreducible_natCast_ratLocalizedAt p hpp
  haveI : IsLocalization.Away ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ℚ := isLocalization_away_of_irreducible _ ℚ hpirr
  have hsm : ∀ (n : ℕ) (y : L), (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ n) • y = (p : L) ^ n * y :=
    fun n y => by rw [Algebra.smul_def, map_pow, map_natCast]
  have hpL : ∀ n : ℕ, ((p : L) ^ n) ≠ 0 := fun n => pow_ne_zero _ (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hRL : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) L r = algebraMap ℚ L (r : ℚ) := fun r => rfl
  set Θ := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) L ↥K') g (fun _ _ => Commute.all _ _)
    with hΘdef
  have hΘ : ∀ (c : L) (b : ↥B), Θ (c ⊗ₜ b) = algebraMap L _ c * g b := fun c b =>
    Algebra.TensorProduct.lift_tmul _ _ _ c b
  have hcoeL : ∀ c : L, algebraMap ↥K' (LaurentSeries L) (algebraMap L ↥K' c) =
      HahnSeries.single 0 c := fun c => by
    rw [← IsScalarTower.algebraMap_apply L ↥K' (LaurentSeries L), algebraMap_laurentSeries_eq_single]
  let bL := Module.finBasis ℚ L

  have hdec : ∀ t : L ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B, ∃ (m : ℕ) (c : Fin (Module.finrank ℚ L) → ↥B),
      t = ∑ i, (((p : L) ^ m)⁻¹ * bL i) ⊗ₜ c i := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul l b =>
      obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exist_integer_multiples_of_finset
        (Submonoid.powers ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) (Finset.univ.image (bL.repr l))
      have hm' : ∀ i, ∃ r : ↥(GaloisRep.ratLocalizedAt p), (r : ℚ) = (p : ℚ) ^ m * bL.repr l i := by
        intro i
        obtain ⟨r, hr⟩ := hm (bL.repr l i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        refine ⟨r, ?_⟩
        rw [Submonoid.smul_def, smul_eq_mul] at hr
        refine hr.trans ?_
        congr 1
      choose r hr using hm'
      refine ⟨m, fun i => r i • b, ?_⟩
      conv_lhs => rw [← bL.sum_repr l]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      rw [Algebra.smul_def, Algebra.smul_def, hRL, hr, map_mul, map_pow, map_natCast, mul_assoc,
        mul_left_comm ((p : L) ^ m), mul_inv_cancel_left₀ (hpL m)]
    | add s t hs ht =>
      obtain ⟨m, c, rfl⟩ := hs
      obtain ⟨m', c', rfl⟩ := ht
      refine ⟨m + m', fun i => ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m' • c i + ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m • c' i, ?_⟩
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m') • (((p : L) ^ (m + m'))⁻¹ * bL i) = ((p : L) ^ m)⁻¹ * bL i := by
        rw [hsm, ← mul_assoc, pow_add, mul_inv_rev, mul_inv_cancel_left₀ (hpL m')]
      have e2 : (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m) • (((p : L) ^ (m + m'))⁻¹ * bL i) = ((p : L) ^ m')⁻¹ * bL i := by
        rw [hsm, ← mul_assoc, pow_add, mul_inv_rev, mul_comm (((p : L) ^ m')⁻¹) _,
          mul_inv_cancel_left₀ (hpL m)]
      rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, e1, e2]
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨m, c, rfl⟩ := hdec t
  have hsum : ∑ i, HahnSeries.single 0 (((p : L) ^ m)⁻¹ * bL i) *
      coeffEmb L (((c i : ↥B) : ↥F₀) : LaurentSeries ℚ) = 0 := by
    have h0 := congrArg (algebraMap ↥K' (LaurentSeries L)) ht
    rw [map_zero, map_sum, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, map_mul (algebraMap ↥K' (LaurentSeries L)), hcoeL, hg]
  have hli : LinearIndependent ℚ (fun i => ((p : L) ^ m)⁻¹ * bL i) :=
    bL.linearIndependent.map' (LinearMap.mulLeft ℚ (((p : L) ^ m)⁻¹))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (inv_ne_zero (hpL m))))
  have hzero := eq_zero_of_sum_single_mul_coeffEmb_eq_zero L Finset.univ _ hli _ hsum
  have hc0 : ∀ i, c i = 0 := fun i => Subtype.ext (Subtype.ext (hzero i (Finset.mem_univ i)))
  simp [hc0]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isReduced_tensor_of_isReduced_quotient (p : ℕ) [hp : Fact p.Prime]
    (B : Type) [CommRing B] [Algebra ↥(GaloisRep.ratLocalizedAt p) B]
    (hred : IsReduced (B ⧸ Ideal.span {((p : ℕ) : B)}))
    (k' : Type) [Field k'] [Algebra ↥(GaloisRep.ratLocalizedAt p) k'] (hpk : algebraMap ↥(GaloisRep.ratLocalizedAt p) k' ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = 0) :
    IsReduced (k' ⊗[↥(GaloisRep.ratLocalizedAt p)] B) := by
  have hpp : p.Prime := hp.out
  haveI hRdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hpp
  have hpirr : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := GaloisRep.irreducible_natCast_ratLocalizedAt p hpp
  have hmaxR : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := hpirr.maximalIdeal_eq
  have hpmax : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) := hmaxR ▸ Ideal.mem_span_singleton_self _
  haveI cp : CharP (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) p :=
    (CharP.charP_iff_prime_eq_zero hpp).mpr (by
      have h := (IsLocalRing.residue_eq_zero_iff _).mpr hpmax
      rwa [map_natCast] at h)
  haveI : CharP (↥(GaloisRep.ratLocalizedAt p) ⧸ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p)) p := cp
  haveI : Finite (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) := finite_quotient_ratLocalizedAt p (IsLocalRing.maximalIdeal _)
  haveI : PerfectField (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) := PerfectField.ofFinite
  letI algk : Algebra (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) k' :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p)) (algebraMap ↥(GaloisRep.ratLocalizedAt p) k')
      (fun r hr => by
        rw [hmaxR] at hr
        obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [map_mul, hpk, mul_zero])).toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) k' :=
    IsScalarTower.of_algebraMap_eq fun r => (Ideal.Quotient.lift_mk _ _ _).symm
  have hJ : Ideal.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) B) (IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p)) = Ideal.span {((p : ℕ) : B)} := by
    rw [hmaxR, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : IsReduced (B ⧸ Ideal.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) B) (IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p))) :=
    isReduced_of_injective (Ideal.quotEquivOfEq hJ) (Ideal.quotEquivOfEq hJ).injective
  let eQ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p))).toRingEquiv
  let eC := (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt p) (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) B).toRingEquiv
  haveI hred0 : IsReduced (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p) ⊗[↥(GaloisRep.ratLocalizedAt p)] B) :=
    isReduced_of_injective (eC.trans eQ.symm).toRingHom (eC.trans eQ.symm).injective
  haveI : IsReduced (k' ⊗[IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)] (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p) ⊗[↥(GaloisRep.ratLocalizedAt p)] B)) :=
    Algebra.isReduced_tensorProduct_of_perfectField _ _ _
  let eB := (Algebra.TensorProduct.cancelBaseChange ↥(GaloisRep.ratLocalizedAt p) (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p))
    (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) k' B).toRingEquiv
  exact isReduced_of_injective eB.symm.toRingHom eB.symm.injective

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem chartAlgFin_le_range (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K]
    (S : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra A S] (ψ : S →ₐ[A] K)
    (hinj : Function.Injective ψ)
    (hfr : ∀ z : K, ∃ (s t : S), z * ψ t = ψ s ∧ t ≠ 0)
    (x' : K) [Fact (x' ≠ 0)] (hx' : x' ∈ ψ.range) :
    TwoChartIntegralModel.chartAlgFin A K x' ≤ ψ.range := by
  letI algS : Algebra S K := ψ.toRingHom.toAlgebra
  have halgS : ∀ t, algebraMap S K t = ψ t := fun _ => rfl
  haveI : FaithfulSMul S K := (faithfulSMul_iff_algebraMap_injective S K).mpr hinj
  haveI : IsFractionRing S K := by
    refine IsFractionRing.of_field S K fun z => ?_
    obtain ⟨s, t, hz, ht⟩ := hfr z
    refine ⟨s, t, ?_⟩
    rw [halgS, halgS, eq_div_iff ((map_ne_zero_iff _ hinj).mpr ht), hz]
  intro y hy
  have hC'le : Algebra.adjoin A ({x'} : Set K) ≤ ψ.range :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx')
  obtain ⟨P, hPm, hPy⟩ := (TwoChartIntegralModel.mem_chartAlg_iff _ _).mp hy
  have hlifts : P.map (algebraMap ↥(Algebra.adjoin A ({x'} : Set K)) K) ∈
      Polynomial.lifts (ψ : S →+* K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨t, ht⟩ := (AlgHom.mem_range ψ).mp (hC'le (P.coeff n).2)
    exact ⟨t, ht⟩
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hPm.map _)
  have hyS : IsIntegral S y := by
    refine ⟨Q, hQm, ?_⟩
    change Polynomial.eval₂ (ψ : S →+* K) y Q = 0
    rw [Polynomial.eval₂_eq_eval_map, hQ, Polynomial.eval_map]
    exact hPy
  obtain ⟨t, ht⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).mp hyS
  exact (AlgHom.mem_range ψ).mpr ⟨t, ht⟩

end ModularCurve.ChartBCAux

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jq jqN jqN_mem modularFunctionFieldFull modularFunctionField_le_full qExpFunctionFieldC algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull"
namespace ChartBCAux
p2m_open "ModularCurve"

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem core (p : ℕ) [hp : Fact p.Prime]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥F₀]
    [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥F₀]
    (x : ↥F₀) (B : Subalgebra ↥(GaloisRep.ratLocalizedAt p) ↥F₀)
    (hB : ∀ y : ↥F₀, y ∈ B ↔
      IsIntegral ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀)) y)
    (hfrac : IsFractionRing ↥B ↥F₀)
    (hred : IsReduced (↥B ⧸ Ideal.span {((p : ℕ) : ↥B)}))
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (hgen : IsDomain (L ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) ∧
      IsIntegrallyClosed (L ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B))
    (K' : IntermediateField L (LaurentSeries L)) (hK' : K' = laurentBaseChange L F₀)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (x' : ↥K') (hx' : ((x' : LaurentSeries L)) = coeffEmb L ((x : ↥F₀) : LaurentSeries ℚ))
    [Fact (x' ≠ 0)] :
    ∃ e : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B ≃ₐ[A] ↥(TwoChartIntegralModel.chartAlgFin A ↥K' x'),
      ∀ b : ↥B, (((e (1 ⊗ₜ b) : ↥K') : LaurentSeries L)) =
        coeffEmb L (((b : ↥F₀) : LaurentSeries ℚ)) := by
  classical
  have hpp : p.Prime := hp.out

  haveI hRdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hpp
  haveI hRpid : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI hRfrac : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hpirr : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) :=
    GaloisRep.irreducible_natCast_ratLocalizedAt p hpp
  have hmaxR : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) =
      Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := hpirr.maximalIdeal_eq
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hpp)
  have hloc := GaloisRep.isLocalization_ratLocalizedAt hpp
  have hext : ∀ {T : Type} [CommRing T] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* T), f = g := by
    intro T _ f g
    exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)
  have hsm : ∀ (n : ℕ) (y : L), (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ n) • y = (p : L) ^ n * y :=
    fun n y => by rw [Algebra.smul_def, map_pow, map_natCast]
  have hpL : ∀ n : ℕ, ((p : L) ^ n) ≠ 0 := fun n => pow_ne_zero _ (Nat.cast_ne_zero.mpr hpp.ne_zero)

  letI algRK : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥K' :=
    ((algebraMap A ↥K').comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)).toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A ↥K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) L ↥K' :=
    IsScalarTower.of_algebraMap_eq fun r => RingHom.congr_fun
      (hext (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥K')
        ((algebraMap L ↥K').comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) L))) r
  have hAinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hcoeL : ∀ c : L, algebraMap ↥K' (LaurentSeries L) (algebraMap L ↥K' c) =
      HahnSeries.single 0 c := fun c => by
    rw [← IsScalarTower.algebraMap_apply L ↥K' (LaurentSeries L), algebraMap_laurentSeries_eq_single]
  have hcoeA : ∀ a : A, algebraMap ↥K' (LaurentSeries L) (algebraMap A ↥K' a) =
      HahnSeries.single 0 (algebraMap A L a) := fun a => by
    rw [IsScalarTower.algebraMap_apply A L ↥K', ← IsScalarTower.algebraMap_apply L ↥K' (LaurentSeries L),
      algebraMap_laurentSeries_eq_single]

  let G₀ : ↥F₀ →+* ↥K' := ((coeffEmb L).comp (algebraMap ↥F₀ (LaurentSeries ℚ))).codRestrict K'
    (fun f => by rw [hK']; exact coeffEmb_mem_laurentBaseChange L f.2)
  have hG₀ : ∀ f : ↥F₀, ((G₀ f : ↥K') : LaurentSeries L) = coeffEmb L (f : LaurentSeries ℚ) := fun _ => rfl
  have hG₀inj : Function.Injective G₀ := fun a b h => by
    have h' := congrArg (fun z : ↥K' => (z : LaurentSeries L)) h
    simp only [hG₀] at h'
    exact Subtype.ext ((coeffEmb L).injective h')
  have hG₀R : G₀.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀) =
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥K' := hext _ _
  have hG₀x : G₀ x = x' := Subtype.ext (by rw [hG₀, hx'])
  let g₀ : ↥B →+* ↥K' := G₀.comp (algebraMap ↥B ↥F₀)
  have hg₀ : ∀ b : ↥B, g₀ b = G₀ (b : ↥F₀) := fun _ => rfl
  have hg₀inj : Function.Injective g₀ := hG₀inj.comp Subtype.val_injective
  have hgcomm : g₀.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥B) =
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥K' := hext _ _
  let g : ↥B →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥K' :=
    { g₀ with commutes' := fun r => RingHom.congr_fun hgcomm r }
  have hgg : ∀ b : ↥B, g b = g₀ b := fun _ => rfl
  have hcoeg : ∀ b : ↥B, algebraMap ↥K' (LaurentSeries L) (g b) =
      coeffEmb L (((b : ↥F₀)) : LaurentSeries ℚ) := fun _ => rfl
  let ψ : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B →ₐ[A] ↥K' :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ (a : A) (b : ↥B), ψ (a ⊗ₜ b) = algebraMap A _ a * g b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b

  have hRF₀ : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ =
      (algebraMap ℚ ↥F₀).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) :=
    IsScalarTower.algebraMap_eq _ _ _
  have hRF₀inj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀) := by
    rw [hRF₀]
    exact (algebraMap ℚ ↥F₀).injective.comp (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ)
  haveI : NoZeroSMulDivisors ↥(GaloisRep.ratLocalizedAt p) ↥B := by
    refine ⟨fun {r b} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      apply hRF₀inj
      rw [map_zero, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ↥B ↥F₀, h, map_zero]
    · exact Or.inr h
  haveI hBflat : Module.Flat ↥(GaloisRep.ratLocalizedAt p) ↥B := inferInstance

  let Θ : L ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥K' :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) L ↥K') g
      (fun _ _ => Commute.all _ _)
  have hΘ : ∀ (c : L) (b : ↥B), Θ (c ⊗ₜ b) = algebraMap L _ c * g b := fun c b =>
    Algebra.TensorProduct.lift_tmul _ _ _ c b
  have hΘinj : Function.Injective Θ := injective_lift_coeffEmb p F₀ B L K' g hcoeg

  let mAL : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B →ₐ[↥(GaloisRep.ratLocalizedAt p)]
      L ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A L) (AlgHom.id _ ↥B)
  have hmALt : ∀ (a : A) (b : ↥B), mAL (a ⊗ₜ b) = algebraMap A L a ⊗ₜ b := fun a b =>
    Algebra.TensorProduct.map_tmul _ _ a b
  have hmAL : Function.Injective mAL := by
    have hlin := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥B)
      ((IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A L).toLinearMap) hAinj
    have heq : ∀ t, mAL t =
        ((IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A L).toLinearMap.rTensor ↥B) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rw [hmALt, LinearMap.rTensor_tmul]; rfl
      | add s t hs ht => simp only [map_add, hs, ht]
    intro s t hst
    apply hlin
    rw [← heq, ← heq, hst]
  have hψΘ : ∀ t, ψ t = Θ (mAL t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [hmALt, hψ, hΘ, IsScalarTower.algebraMap_apply A L ↥K']
    | add s t hs ht => simp only [map_add, hs, ht]
  have hinj : Function.Injective ψ := fun s t hst =>
    hmAL (hΘinj (by rw [← hψΘ, ← hψΘ, hst]))

  have hle : ψ.range ≤ TwoChartIntegralModel.chartAlgFin A ↥K' x' := by
    set C := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀) with hC
    set C' := Algebra.adjoin A ({x'} : Set ↥K') with hC'
    have hCC' : C.toSubring.map G₀ ≤ C'.toSubring := by
      rw [Subring.map_le_iff_le_comap]
      have h1 : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
          algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r ∈ C'.toSubring.comap G₀ := by
        intro r
        change G₀ (algebraMap _ _ r) ∈ C'
        have : G₀ (algebraMap _ _ r) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥K' r :=
          RingHom.congr_fun hG₀R r
        rw [this, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) A ↥K']
        exact Subalgebra.algebraMap_mem C' _
      let D : Subalgebra ↥(GaloisRep.ratLocalizedAt p) ↥F₀ :=
        { C'.toSubring.comap G₀ with
          algebraMap_mem' := h1 }
      have hxD : x ∈ D := by change G₀ x ∈ C'; rw [hG₀x]; exact Algebra.subset_adjoin rfl
      have hCD : C ≤ D := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxD)
      intro c hc
      exact hCD hc
    have hint : ∀ b : ↥B, IsIntegral C' ((g₀ b : ↥K')) := by
      intro b
      have hb : IsIntegral C ((b : ↥F₀)) := (hB _).mp b.2
      let φ : C →+* C' := (Subring.inclusion hCC').comp ((G₀.restrict C.toSubring (C.toSubring.map G₀)
        fun c hc => Subring.mem_map.mpr ⟨c, hc, rfl⟩))
      refine hb.map_of_comp_eq φ G₀ ?_
      ext c; rfl
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b =>
      change ψ (a ⊗ₜ b) ∈ _
      rw [hψ]
      refine mul_mem (Subalgebra.algebraMap_mem _ a) ?_
      exact (TwoChartIntegralModel.mem_chartAlg_iff _ _).mpr (hint b)
    | add s t hs ht => rw [map_add]; exact add_mem hs ht

  have hge : TwoChartIntegralModel.chartAlgFin A ↥K' x' ≤ ψ.range := by

    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
    have hmaxA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    haveI : IsLocalization.Away ϖ L := isLocalization_away_of_irreducible A L hϖ
    letI algRk : Algebra ↥(GaloisRep.ratLocalizedAt p) (IsLocalRing.ResidueField A) :=
      ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)).toAlgebra
    haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A (IsLocalRing.ResidueField A) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI := hgen.1
    haveI := hgen.2
    have hpk : algebraMap ↥(GaloisRep.ratLocalizedAt p) (IsLocalRing.ResidueField A) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = 0 := by
      rw [map_natCast]
      have h := (IsLocalRing.residue_eq_zero_iff (p : A)).mpr hAp
      rwa [map_natCast] at h
    have hred' : IsReduced (IsLocalRing.ResidueField A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) :=
      isReduced_tensor_of_isReduced_quotient p ↥B hred (IsLocalRing.ResidueField A) hpk

    obtain ⟨hdom, hic⟩ := Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre
      (R := ↥(GaloisRep.ratLocalizedAt p)) (B := ↥B) (R' := A) (K' := L)
      (k' := IsLocalRing.ResidueField A) ϖ (mem_nonZeroDivisors_of_ne_zero hϖ0)
      IsLocalRing.residue_surjective ((IsLocalRing.ker_residue (R := A)).trans hmaxA) hred'
    haveI := hdom
    haveI := hic

    have hfr : ∀ z : ↥K', ∃ (s t : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B), z * ψ t = ψ s ∧ t ≠ 0 := by
      intro z
      have hz : (z : LaurentSeries L) ∈ laurentBaseChange L F₀ := hK' ▸ z.2
      obtain ⟨n, c, f, hf, hz'⟩ :=
        exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange L F₀ (z : LaurentSeries L) hz
      obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
        (Finset.univ.image c)
      obtain ⟨⟨e, he⟩, hef⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ↥B)
        (Finset.univ.image fun i => (⟨f i, hf i⟩ : ↥F₀))
      have ha' : ∀ i, ∃ a : A, algebraMap A L a = algebraMap A L d * c i := by
        intro i
        obtain ⟨a, ha⟩ := hdc (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        exact ⟨a, by rw [ha, Algebra.smul_def]⟩
      have hb' : ∀ i, ∃ b : ↥B, ((b : ↥F₀) : LaurentSeries ℚ) = ((e : ↥F₀) : LaurentSeries ℚ) * f i := by
        intro i
        obtain ⟨b, hb⟩ := hef ⟨f i, hf i⟩ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        refine ⟨b, ?_⟩
        have hb2 : algebraMap ↥B ↥F₀ b = (e : ↥F₀) * ⟨f i, hf i⟩ := by
          rw [hb]; rfl
        exact congrArg (fun w : ↥F₀ => (w : LaurentSeries ℚ)) hb2
      choose a ha using ha'
      choose b hb using hb'
      have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
      have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
      have hde : ψ (d ⊗ₜ e) ≠ 0 := by
        rw [hψ]
        refine mul_ne_zero ?_ ?_
        · rw [IsScalarTower.algebraMap_apply A L ↥K']
          exact (map_ne_zero _).mpr ((map_ne_zero_iff _ hAinj).mpr hd0)
        · rw [hgg]
          exact (map_ne_zero_iff _ hg₀inj).mpr he0
      have hterm : ∀ i, algebraMap ↥K' (LaurentSeries L) (ψ (a i ⊗ₜ b i)) =
          (HahnSeries.single 0 (c i) * coeffEmb L (f i)) *
            (HahnSeries.single 0 (algebraMap A L d) * coeffEmb L ((e : ↥F₀) : LaurentSeries ℚ)) := by
        intro i
        rw [hψ, map_mul (algebraMap ↥K' (LaurentSeries L)), hcoeA, hcoeg, ha, hb, map_mul (coeffEmb L)]
        simp only [← algebraMap_laurentSeries_eq_single]
        rw [map_mul (algebraMap L (LaurentSeries L))]
        generalize algebraMap L (LaurentSeries L) (algebraMap A L d) = P₁
        generalize algebraMap L (LaurentSeries L) (c i) = P₂
        generalize coeffEmb L ((e : ↥F₀) : LaurentSeries ℚ) = X₁
        generalize coeffEmb L (f i) = X₂
        ring
      refine ⟨∑ i, a i ⊗ₜ b i, d ⊗ₜ e, ?_, fun h0 => hde (by rw [h0, map_zero])⟩
      apply Subtype.ext
      change algebraMap ↥K' (LaurentSeries L) (z * ψ (d ⊗ₜ e)) =
        algebraMap ↥K' (LaurentSeries L) (ψ (∑ i, a i ⊗ₜ b i))
      rw [map_mul (algebraMap ↥K' (LaurentSeries L)), map_sum, map_sum,
        Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul, hψ,
        map_mul (algebraMap ↥K' (LaurentSeries L)), hcoeA, hcoeg, ← hz']
      rfl

    have hxB : x ∈ B := (hB x).mpr (isIntegral_algebraMap
      (R := ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀)))
      (x := ⟨x, Algebra.self_mem_adjoin_singleton _ x⟩))
    have hx'r : x' ∈ ψ.range := by
      refine ⟨(1 : A) ⊗ₜ (⟨x, hxB⟩ : ↥B), ?_⟩
      change ψ ((1 : A) ⊗ₜ (⟨x, hxB⟩ : ↥B)) = x'
      rw [hψ, map_one, one_mul]
      exact hG₀x
    exact chartAlgFin_le_range A ↥K' (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) ψ hinj hfr x' hx'r

  have hrange : ψ.range = TwoChartIntegralModel.chartAlgFin A ↥K' x' := le_antisymm hle hge
  refine ⟨(AlgEquiv.ofInjective ψ hinj).trans (Subalgebra.equivOfEq _ _ hrange), fun b => ?_⟩
  change (((ψ (1 ⊗ₜ b)) : ↥K') : LaurentSeries L) = _
  rw [hψ, map_one, one_mul]
  rfl

end ModularCurve.ChartBCAux

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jq jqN jqN_mem modularFunctionFieldFull modularFunctionField_le_full qExpFunctionFieldC algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull mem_chartAlg_iff adjoin_le_chartAlg subset_chartAlg chartAlgFin isIntegrallyClosed_tensor_chartAlgFin_of_charZero isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd exists_mul_mem_adjoin_jFull_jqN jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN"
p2m_open "ModularCurve.IgusaScheme ModularCurve"

theorem isFractionRing_chartAlgFin' (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsFractionRing ↥(chartAlgFin N ℓ) ↥(modularFunctionFieldFull N) := by
  have hjN := (jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN N ℓ).1
  have hle : Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ)
      ({jFull N, ⟨jqN N, modularFunctionField_le_full N (jqN_mem N)⟩} : Set ↥(modularFunctionFieldFull N)) ≤
      chartAlgFin N ℓ := by
    refine Algebra.adjoin_le ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact subset_chartAlg N ℓ _ rfl
    · exact hjN
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.mpr fun h => nonZeroDivisors.ne_zero hy (Subtype.ext h)
  · intro x
    obtain ⟨g, hg, hg0, hgx⟩ := exists_mul_mem_adjoin_jFull_jqN N ℓ x
    have hgA : g ∈ chartAlgFin N ℓ := adjoin_le_chartAlg N ℓ _ hg
    have hgxA : g * x ∈ chartAlgFin N ℓ := hle hgx
    refine ⟨(⟨g * x, hgxA⟩, ⟨⟨g, hgA⟩, mem_nonZeroDivisors_of_ne_zero fun h => hg0 ?_⟩), ?_⟩
    · exact congrArg Subtype.val h
    · change x * g = g * x
      exact mul_comm _ _
  · intro a b h
    exact ⟨1, by rw [Subtype.ext h]⟩

end ModularCurve.IgusaScheme

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd.ModularCurve.IgusaScheme AlgebraicCurve in

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (N * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j' ≠ 0)] :
    ∃ e : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) ≃ₐ[A]
        ↥(TwoChartIntegralModel.chartAlgFin A ↥K' j'),
      ∀ b : ↥(chartAlgFin (N * p) p),
        (((e (1 ⊗ₜ b) : ↥(TwoChartIntegralModel.chartAlgFin A ↥K' j')) : ↥K') : LaurentSeries L) =
          ModularCurve.coeffEmb L (((b : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ)) := by
  rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull (N * p)] at hK'
  obtain ⟨hred, -, -, -⟩ := isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd N p hpN
  exact ModularCurve.ChartBCAux.core p (modularFunctionFieldFull (N * p)) (jFull (N * p)) (chartAlgFin (N * p) p)
    (fun _ => mem_chartAlg_iff (N * p) p) (isFractionRing_chartAlgFin' (N * p) p) hred L
    (isIntegrallyClosed_tensor_chartAlgFin_of_charZero (N * p) p L) K' hK' A hAp j'
    (by rw [hj', coe_jFull])

set_option maxHeartbeats 1600000 in
#print axioms solution

end S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgFin_mul_chartAlgFin_laurentBaseChange_of_not_dvd (solution)
