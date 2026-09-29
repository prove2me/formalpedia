-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8674c6cb-a70a-5034-b944-fa1f5b60064c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero_divisorClassGroup
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~isAlgebraic_adjoin_of_transcendental"
p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin.ModularCurve ModularCurve.XHDRLevel"
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial MatrixGroups"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.jChartFin XHDRModelAtP translation_mem_GammaH qExpFunctionFieldC qExpand dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffMap_ofPowerSeries jqModC jqModC_rat coeffMap_qExpand deltaSeries modularUnitSeries isMonicOfOrder_modularUnitSeries modularUnitSeries_ne_zero coeffEmb_qExpand exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "iota0_spec w isIntegral π iota0 mk comp"
namespace QFibreUnramH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

section Generic

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]

private theorem exists_ne_zero_forall_smul_kaehler_eq_zero
    (L : Type*) [Field L] [Algebra A L] [Algebra R L] [IsScalarTower R A L] [IsFractionRing A L]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R L] :
    ∃ a : A, a ≠ 0 ∧ ∀ ω : Ω[A⁄R], a • ω = 0 := by
  classical
  have htor : ∀ ω : Ω[A⁄R], ∃ s : nonZeroDivisors A, (s : A) • ω = 0 := fun ω =>
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) (KaehlerDifferential.map R R A L)).mp
      (Subsingleton.elim _ _)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Ω[A⁄R])
  choose c hc using htor
  refine ⟨∏ ω ∈ s, (c ω : A), Finset.prod_ne_zero_iff.mpr fun ω _ => nonZeroDivisors.coe_ne_zero (c ω), ?_⟩
  intro ω
  have hmem : ω ∈ Submodule.span A (s : Set Ω[A⁄R]) := by rw [hs]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht⟩ : (c y : A) ∣ ∏ ω ∈ s, (c ω : A) := Finset.dvd_prod_of_mem _ hy
    rw [ht, mul_comm, mul_smul, hc, smul_zero]
  | zero => exact smul_zero _
  | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
  | smul r y _ hy => rw [smul_comm, hy, smul_zero]

private theorem exists_ne_zero_algebraMap_mem_span {a : A} (ha0 : a ≠ 0) (ha : IsAlgebraic R a) :
    ∃ c : R, c ≠ 0 ∧ algebraMap R A c ∈ Ideal.span {a} := by
  obtain ⟨P, hP0, hPa⟩ := ha
  obtain ⟨Q, hPQ, hQ⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 0
  rw [map_zero, sub_zero] at hPQ hQ
  rw [Polynomial.X_dvd_iff] at hQ
  have hQa : Polynomial.aeval a Q = 0 := by
    rw [hPQ, map_mul, map_pow, Polynomial.aeval_X] at hPa
    exact (mul_eq_zero.mp hPa).resolve_left (pow_ne_zero _ ha0)
  refine ⟨Q.coeff 0, hQ, ?_⟩
  have h := congrArg (Polynomial.aeval a) (Polynomial.X_mul_divX_add Q)
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hQa] at h
  have : algebraMap R A (Q.coeff 0) = a * (-(Polynomial.aeval a Q.divX)) := by
    rw [mul_neg]; exact eq_neg_of_add_eq_zero_right h
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)

omit [IsDomain A] in

private theorem formallyUnramified_quotient_of_forall_smul_eq_zero {a : A} (ha : ∀ ω : Ω[A⁄R], a • ω = 0)
    (I : Ideal A) (hu : IsUnit (Ideal.Quotient.mk I a)) : Algebra.FormallyUnramified R (A ⧸ I) := by
  refine ⟨⟨fun ω₁ ω₂ => ?_⟩⟩
  suffices h : ∀ ω : Ω[(A ⧸ I)⁄R], ω = 0 by rw [h ω₁, h ω₂]
  intro ω
  obtain ⟨ω₀, rfl⟩ := KaehlerDifferential.map_surjective_of_surjective R R A (A ⧸ I) Ideal.Quotient.mk_surjective ω
  have h1 : (Ideal.Quotient.mk I a) • KaehlerDifferential.map R R A (A ⧸ I) ω₀ = 0 := by
    have := congrArg (KaehlerDifferential.map R R A (A ⧸ I)) (ha ω₀)
    rw [map_zero] at this
    rw [← this, LinearMap.map_smul_of_tower]
    rfl
  exact (hu.smul_left_cancel).mp (h1.trans (smul_zero _).symm)

end Generic

section Laurent

variable {k : Type*} [Field k]

private def MonicAt (f : LaurentSeries k) (m : ℤ) : Prop := f.order = m ∧ f.coeff m = 1

private theorem MonicAt.ne_zero {f : LaurentSeries k} {m : ℤ} (h : MonicAt f m) : f ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (g := m) (by rw [h.2]; exact one_ne_zero)

private theorem MonicAt.leadingCoeff {f : LaurentSeries k} {m : ℤ} (h : MonicAt f m) : f.leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, h.1, h.2]

private theorem MonicAt.coeff_of_lt {f : LaurentSeries k} {m i : ℤ} (h : MonicAt f m) (hi : i < m) : f.coeff i = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_order (h.1 ▸ hi)

private theorem MonicAt.of_coeff {f : LaurentSeries k} {m : ℤ} (h1 : f.coeff m = 1) (h0 : ∀ i < m, f.coeff i = 0) :
    MonicAt f m := by
  refine ⟨le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)) ?_, h1⟩
  by_contra hlt
  rw [not_le] at hlt
  have hne : f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (g := m) (by rw [h1]; exact one_ne_zero)
  exact hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

private theorem MonicAt.one : MonicAt (1 : LaurentSeries k) 0 :=
  MonicAt.of_coeff (by simp) (fun i hi => by
    rw [← HahnSeries.single_zero_one, HahnSeries.coeff_single_of_ne hi.ne])

private theorem MonicAt.mul {f g : LaurentSeries k} {m n : ℤ} (hf : MonicAt f m) (hg : MonicAt g n) :
    MonicAt (f * g) (m + n) := by
  have h1 : f.leadingCoeff * g.leadingCoeff ≠ 0 := by
    rw [hf.leadingCoeff, hg.leadingCoeff, one_mul]; exact one_ne_zero
  have ho : (f * g).order = m + n := by rw [HahnSeries.order_mul_of_ne_zero h1, hf.1, hg.1]
  refine ⟨ho, ?_⟩
  have := HahnSeries.leadingCoeff_mul_of_ne_zero h1
  rw [hf.leadingCoeff, hg.leadingCoeff, one_mul, HahnSeries.leadingCoeff_eq, ho] at this
  exact this

private theorem MonicAt.pow {f : LaurentSeries k} {m : ℤ} (hf : MonicAt f m) (i : ℕ) : MonicAt (f ^ i) (i * m) := by
  induction i with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact MonicAt.one
  | succ n ih => rw [pow_succ, Nat.cast_succ, add_mul, one_mul]; exact ih.mul hf

private theorem MonicAt.transcendental {f : LaurentSeries k} {m : ℤ} (hf : MonicAt f m) (hm : m < 0) :
    Transcendental k f := by
  rintro ⟨P, hP0, hP⟩
  apply Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hcoeff : (Polynomial.aeval f P).coeff ((P.natDegree : ℤ) * m) = P.leadingCoeff := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single P.natDegree]
    · rw [Algebra.smul_def, ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        (hf.pow P.natDegree).2, mul_one, Polynomial.leadingCoeff]
    · intro i hi hne
      have hid : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      have hlt : (P.natDegree : ℤ) * m < (i : ℤ) * m := mul_lt_mul_of_neg_right (by exact_mod_cast hid) hm
      rw [Algebra.smul_def, ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        (hf.pow i).coeff_of_lt hlt, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  rw [← hcoeff, hP, HahnSeries.coeff_zero]

private theorem MonicAt.valuation {f : LaurentSeries k} {m : ℤ} (hf : MonicAt f m) :
    Valued.v f = WithZero.exp (-m) := by
  have hle : Valued.v f ≤ WithZero.exp (-m) :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mpr (fun n hn => hf.coeff_of_lt hn)
  have hnot : ¬ Valued.v f ≤ WithZero.exp (-(m + 1)) := fun h => by
    have := ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mp h) m (by omega)
    rw [hf.2] at this; exact one_ne_zero this
  have h0 : Valued.v f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf.ne_zero
  rw [← WithZero.exp_log h0] at hle hnot ⊢
  rw [WithZero.exp_le_exp] at hle
  rw [WithZero.exp_le_exp, not_le] at hnot
  rw [WithZero.exp_inj]
  omega

end Laurent

section ValuationHelpers

variable {K : Type*} [Field K]

private theorem isUnit_iff_inv_mem (V : ValuationSubring K) {a : K} (ha : a ∈ V) (ha0 : a ≠ 0) :
    IsUnit (⟨a, ha⟩ : V) ↔ a⁻¹ ∈ V := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : ((↑u⁻¹ : V) : K) * a = 1 := by
      have := congrArg (fun y : V => (y : K)) u.inv_mul
      simpa [hu] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

private theorem mem_nonunits_iff' (V : ValuationSubring K) (a : K) :
    a ∈ V.nonunits ↔ a ∈ V ∧ (a = 0 ∨ a⁻¹ ∉ V) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨ha, ?_⟩
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · right
      intro hinv
      exact ((IsLocalRing.mem_maximalIdeal _).mp hm) ((isUnit_iff_inv_mem V ha ha0).mpr hinv)
  · rintro ⟨ha, h⟩
    refine ⟨ha, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
    rcases h with h0 | hinv
    · subst h0
      exact not_isUnit_zero (by
        have : (⟨(0 : K), ha⟩ : V) = 0 := Subtype.ext rfl
        rwa [this] at hu)
    · have ha0 : a ≠ 0 := by
        rintro rfl
        have : (⟨(0 : K), ha⟩ : V) = 0 := Subtype.ext rfl
        rw [this] at hu; exact not_isUnit_zero hu
      exact hinv ((isUnit_iff_inv_mem V ha ha0).mp hu)

private theorem mem_of_mem_nonunits (V : ValuationSubring K) {a : K} (h : a ∈ V.nonunits) : a ∈ V :=
  ((mem_nonunits_iff' V a).mp h).1

private theorem not_mem_nonunits_of_inv_mem (V : ValuationSubring K) {a : K} (ha0 : a ≠ 0)
    (h : a⁻¹ ∈ V) : a ∉ V.nonunits := fun hn =>
  ((mem_nonunits_iff' V a).mp hn).2.elim ha0 (fun h' => h' h)

private theorem mul_mem_nonunits (V : ValuationSubring K) {a b : K} (ha : a ∈ V.nonunits) (hb : b ∈ V) :
    a * b ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at ha ⊢
  rw [map_mul]
  calc V.valuation a * V.valuation b ≤ V.valuation a * 1 :=
        mul_le_mul_right ((V.valuation_le_one_iff b).mpr hb) _
    _ = V.valuation a := mul_one _
    _ < 1 := ha

private theorem add_mem_nonunits (V : ValuationSubring K) {a b : K} (ha : a ∈ V.nonunits)
    (hb : b ∈ V.nonunits) : a + b ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at ha hb ⊢
  exact Valuation.map_add_lt _ ha hb

private theorem zero_mem_nonunits (V : ValuationSubring K) : (0 : K) ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one

private theorem pow_mem_nonunits (V : ValuationSubring K) {a : K} (ha : a ∈ V.nonunits) {n : ℕ}
    (hn : n ≠ 0) : a ^ n ∈ V.nonunits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ']
  exact mul_mem_nonunits V ha (pow_mem (mem_of_mem_nonunits V ha) m)

private theorem mem_of_isIntegral_of_le (V : ValuationSubring K) {R : Subring K} (hR : R ≤ V.toSubring)
    {x : K} (hx : IsIntegral R x) : x ∈ V := by
  have hx' : IsIntegral V.toSubring x :=
    hx.map_of_comp_eq (Subring.inclusion hR) (RingHom.id K) (by ext; rfl)
  haveI : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := V.toSubring) (A := K)).mp hx'
  rw [← hy]; exact y.2

end ValuationHelpers

section Fibre

variable {q : ℕ} [Fact q.Prime]
variable {A : Type} [CommRing A] (P : Ideal A) [P.IsPrime]
variable (θ : A →+* LaurentSeries (ZMod q)) (hθ : RingHom.ker θ = P) (hqP : ((q : ℕ) : A) ∈ P)

set_option quotPrecheck false in
local notation "k" => ZMod q
set_option quotPrecheck false in
local notation "L" => LaurentSeries (ZMod q)
set_option quotPrecheck false in
local notation "B" => A ⧸ P
set_option quotPrecheck false in
local notation "E" => FractionRing (A ⧸ P)

include hqP in
private theorem charP_quotient : CharP B q := by
  haveI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr ?_
  have : ((q : ℕ) : B) = Ideal.Quotient.mk P ((q : ℕ) : A) := by rw [map_natCast]
  rw [this, Ideal.Quotient.eq_zero_iff_mem]
  exact hqP

include hqP in

@[reducible] private def algebraK : Algebra k B := by
  haveI := charP_quotient P hqP
  exact (ZMod.castHom (dvd_refl q) B).toAlgebra

private def thetaBar : B →+* L :=
  Ideal.Quotient.lift P θ fun a ha => by rw [← RingHom.mem_ker, hθ]; exact ha

private theorem thetaBar_mk (a : A) : thetaBar P θ hθ (Ideal.Quotient.mk P a) = θ a :=
  Ideal.Quotient.lift_mk _ _ _

private theorem thetaBar_injective : Function.Injective (thetaBar P θ hθ) := by
  rw [thetaBar, Ideal.injective_lift_iff, hθ]

private def iota : E →+* L := IsFractionRing.lift (thetaBar_injective P θ hθ)

private theorem iota_algebraMap (b : B) : iota P θ hθ (algebraMap B E b) = thetaBar P θ hθ b :=
  IsFractionRing.lift_algebraMap _ b

end Fibre

section Coordinate

variable {q : ℕ} [Fact q.Prime]
variable {A : Type} [CommRing A] (P : Ideal A) [P.IsPrime]
variable (θ : A →+* LaurentSeries (ZMod q)) (hθ : RingHom.ker θ = P)
variable [Algebra (ZMod q) (A ⧸ P)]

set_option quotPrecheck false in
local notation "k" => ZMod q
set_option quotPrecheck false in
local notation "L" => LaurentSeries (ZMod q)
set_option quotPrecheck false in
local notation "B" => A ⧸ P
set_option quotPrecheck false in
local notation "E" => FractionRing (A ⧸ P)

private theorem algebraMap_comp_eq : (iota P θ hθ).comp (algebraMap k E) = algebraMap k L :=
  RingHom.ext_zmod _ _

private theorem iota_algebraMap_k (c : k) : iota P θ hθ (algebraMap k E c) = algebraMap k L c :=
  RingHom.congr_fun (algebraMap_comp_eq P θ hθ) c

private def coord (u : A) : E := algebraMap B E (Ideal.Quotient.mk P u)

private theorem iota_coord (u : A) : iota P θ hθ (coord P u) = θ u := by
  rw [coord, iota_algebraMap, thetaBar_mk]

include hθ in

private theorem transcendental_coord (u : A) {m : ℤ} (hm : MonicAt (θ u) m) (hm0 : m < 0) :
    Transcendental k (coord P u) := by
  have hT : Transcendental k (iota P θ hθ (coord P u)) := by rw [iota_coord]; exact hm.transcendental hm0
  exact Transcendental.of_ringHom_of_comp_eq (RingHom.id k) (iota P θ hθ) hT (RingHom.id k).injective
    (RingHom.ext fun c => by simpa using (iota_algebraMap_k P θ hθ c).symm)

private def wval : Valuation E (WithZero (Multiplicative ℤ)) := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).comap (iota P θ hθ)

private theorem wval_apply (e : E) : wval P θ hθ e = Valued.v (iota P θ hθ e) := rfl

private theorem wval_coord (u : A) {m : ℤ} (hm : MonicAt (θ u) m) : wval P θ hθ (coord P u) = WithZero.exp (-m) := by
  rw [wval_apply, iota_coord, hm.valuation]

private theorem wval_algebraMap_le (c : k) : wval P θ hθ (algebraMap k E c) ≤ 1 := by
  rw [wval_apply, iota_algebraMap_k, ModularCurve.algebraMap_laurentSeries_eq_single]
  have : Valued.v (HahnSeries.single (0 : ℤ) c : L) ≤ WithZero.exp (-(0 : ℤ)) :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (ZMod q)).mpr fun n hn => HahnSeries.coeff_single_of_ne hn.ne
  simpa using this

private def place (u : A) {m : ℤ} (hm : MonicAt (θ u) m) (hm0 : m < 0) : AlgebraicCurve.Place k E where
  toValuationSubring := (wval P θ hθ).valuationSubring
  algebraMap_mem' c := by
    rw [Valuation.mem_valuationSubring_iff]; exact wval_algebraMap_le P θ hθ c
  ne_top' := by
    intro htop
    have ht : coord P u ∈ (wval P θ hθ).valuationSubring := htop ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, wval_coord P θ hθ u hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ht
    omega
  isPrincipalIdealRing' := by
    haveI : (wval P θ hθ).IsNontrivial := by
      refine ⟨coord P u, ?_, ?_⟩
      · rw [wval_coord P θ hθ u hm]; exact WithZero.exp_ne_zero
      · rw [wval_coord P θ hθ u hm, Ne, WithZero.exp_eq_one]; omega
    exact Valuation.valuationSubring_isPrincipalIdealRing _

private theorem place_toValuationSubring (u : A) {m : ℤ} (hm : MonicAt (θ u) m) (hm0 : m < 0) :
    (place P θ hθ u hm hm0).toValuationSubring = (wval P θ hθ).valuationSubring := rfl

private theorem wval_unit (x : ((wval P θ hθ).valuationSubring)ˣ) :
    wval P θ hθ ((x : (wval P θ hθ).valuationSubring) : E) = 1 := by
  have h1 : wval P θ hθ ((x : (wval P θ hθ).valuationSubring) : E) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff _ _).mp (x : (wval P θ hθ).valuationSubring).2
  have h2 : wval P θ hθ ((↑(x⁻¹) : (wval P θ hθ).valuationSubring) : E) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff _ _).mp (↑(x⁻¹) : (wval P θ hθ).valuationSubring).2
  have hmul : wval P θ hθ ((x : (wval P θ hθ).valuationSubring) : E) *
      wval P θ hθ ((↑(x⁻¹) : (wval P θ hθ).valuationSubring) : E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact (wval P θ hθ).map_one
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ wval P θ hθ ((x : (wval P θ hθ).valuationSubring) : E) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem ord_coord (u : A) {m : ℤ} (hm : MonicAt (θ u) m) (hm0 : m < 0) (hmq : -m < q) :
    (place P θ hθ u hm hm0).ord (coord P u) ≠ 0 ∧
      ((((place P θ hθ u hm hm0).ord (coord P u)).natAbs : ℕ) : k) ≠ 0 := by
  set v := place P θ hθ u hm hm0 with hv
  have ht0 : coord P u ≠ 0 := fun h => by
    have := wval_coord P θ hθ u hm; rw [h, map_zero] at this; exact WithZero.exp_ne_zero this.symm

  have htinv : (coord P u)⁻¹ ∈ v.toValuationSubring := by
    rw [place_toValuationSubring, Valuation.mem_valuationSubring_iff, map_inv₀, wval_coord P θ hθ u hm,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    exact hm0.le
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u₀, hu₀⟩ := v.exists_unit_mul_zpow (inv_ne_zero ht0) hπ

  have hπ0 : (π : E) ≠ 0 := by
    intro h; apply hπ.ne_zero; exact_mod_cast h
  have hπlt : wval P θ hθ (π : E) < 1 := by
    have hπmem : (π : E) ∈ v.toValuationSubring := π.2
    have hnotunit : ¬ IsUnit π := hπ.not_isUnit
    by_contra hge
    rw [not_lt] at hge
    have hπle : wval P θ hθ (π : E) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).mp π.2
    have heq : wval P θ hθ (π : E) = 1 := le_antisymm hπle hge
    apply hnotunit
    have hinv : (π : E)⁻¹ ∈ (wval P θ hθ).valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, heq, inv_one]
    exact (isUnit_iff_inv_mem ((wval P θ hθ).valuationSubring) π.2 hπ0).mpr hinv
  set e : ℤ := - WithZero.log (wval P θ hθ (π : E)) with he
  have hwπ : wval P θ hθ (π : E) = WithZero.exp (-e) := by
    rw [he, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hπ0)]
  have he1 : 1 ≤ e := by
    rw [hwπ, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hπlt; omega
  set n : ℤ := v.ord (coord P u)⁻¹ with hn
  have key : WithZero.exp m = WithZero.exp (-e) ^ n := by
    have h := congrArg (wval P θ hθ) hu₀
    rw [map_inv₀, wval_coord P θ hθ u hm, ← WithZero.exp_neg, neg_neg, map_mul, map_zpow₀] at h
    rw [h, hwπ]
    have : wval P θ hθ ((u₀ : v.toValuationSubring) : E) = 1 := wval_unit P θ hθ u₀
    rw [this, one_mul]
  rw [← WithZero.exp_zsmul, WithZero.exp_inj, smul_eq_mul] at key

  have hord : v.ord (coord P u) = -n := by rw [hn, v.ord_inv, neg_neg]
  have hn1 : 1 ≤ n := by nlinarith
  have hnq : n < q := by nlinarith
  refine ⟨by rw [hord]; omega, ?_⟩
  rw [hord, Int.natAbs_neg]
  have hnn : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg (by omega)
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (by omega) h0
  omega

include hθ in

private theorem isSeparable_coord (u : A) {m : ℤ} (hm : MonicAt (θ u) m) (hm0 : m < 0) (hmq : -m < q)
    [Algebra.IsAlgebraic (IntermediateField.adjoin k ({coord P u} : Set E)) E] :
    Algebra.IsSeparable (IntermediateField.adjoin k ({coord P u} : Set E)) E :=
  haveI : Fact (Nat.Prime q) := inferInstance
  AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero_divisorClassGroup (coord P u)
    (place P θ hθ u hm hm0) (ord_coord P θ hθ u hm hm0 hmq).1 (ord_coord P θ hθ u hm hm0 hmq).2

end Coordinate

section TrDeg

variable {k E : Type} [Field k] [Field E] [Algebra k E]

open scoped IntermediateField.algebraAdjoinAdjoin in

private theorem isAlgebraic_adjoin_of_transcendental (y x : E)
    [Algebra.IsAlgebraic (IntermediateField.adjoin k ({y} : Set E)) E] (hx : Transcendental k x) :
    Algebra.IsAlgebraic (IntermediateField.adjoin k ({x} : Set E)) E := by
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k ({y} : Set E)) E :=
    Algebra.IsAlgebraic.trans (R := Algebra.adjoin k ({y} : Set E)) (S := IntermediateField.adjoin k ({y} : Set E)) (A := E)
  have htr : Algebra.trdeg k E ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk k ({y} : Set E)
    rwa [Cardinal.mk_singleton] at h
  have h1 : AlgebraicIndependent k ![x] := algebraicIndependent_iff_transcendental.mpr hx
  have hb : IsTranscendenceBasis k ![x] := h1.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have h := hb.isAlgebraic_field
  have hr : Set.range ![x] = {x} := by simp
  rwa [hr] at h

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in

private theorem isFractionRing_polynomial_adjoin (x : E) (hx : Transcendental k x) :
    letI : Algebra k[X] (IntermediateField.adjoin k ({x} : Set E)) :=
      (Polynomial.aeval (IntermediateField.AdjoinSimple.gen k x)).toRingHom.toAlgebra
    IsFractionRing k[X] (IntermediateField.adjoin k ({x} : Set E)) := by
  letI : Algebra k[X] (IntermediateField.adjoin k ({x} : Set E)) :=
    (Polynomial.aeval (IntermediateField.AdjoinSimple.gen k x)).toRingHom.toAlgebra
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental k E x hx
  have halg : ∀ f : k[X], algebraMap k[X] (RatFunc k) f = Polynomial.aeval RatFunc.X f := fun f => by
    have h1 := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k k[X] (RatFunc k)) Polynomial.X f
    rw [Polynomial.aeval_X_left, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_X] at h1
    exact h1.symm
  have hcomm : ∀ f : k[X], e.symm.toRingEquiv (algebraMap k[X] (RatFunc k) f) =
      algebraMap k[X] (IntermediateField.adjoin k ({x} : Set E)) f := by
    intro f
    change e.symm.toRingEquiv (algebraMap k[X] (RatFunc k) f) = Polynomial.aeval (IntermediateField.AdjoinSimple.gen k x) f
    rw [halg, AlgEquiv.coe_ringEquiv, ← Polynomial.aeval_algHom_apply, ← he, AlgEquiv.symm_apply_apply]
    rfl
  let e' : RatFunc k ≃ₐ[k[X]] (IntermediateField.adjoin k ({x} : Set E)) := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) hcomm
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors k[X]) e'

end TrDeg

section Unram

variable {q : ℕ} [Fact q.Prime]
variable {A : Type} [CommRing A] (P : Ideal A) [P.IsPrime]
variable (θ : A →+* LaurentSeries (ZMod q)) (hθ : RingHom.ker θ = P)
variable [Algebra (ZMod q) (A ⧸ P)]

set_option quotPrecheck false in
local notation "k" => ZMod q
set_option quotPrecheck false in
local notation "B" => A ⧸ P
set_option quotPrecheck false in
local notation "E" => FractionRing (A ⧸ P)

private theorem formallyUnramified_of_polynomial {S : Type} [CommRing S] [Algebra k S] (x : S)
    [hX : letI := (Polynomial.aeval (R := k) x).toRingHom.toAlgebra; Algebra.FormallyUnramified k[X] S]
    (g : k[X]) (hsep : g.Separable) (hg : Polynomial.aeval x g = 0) : Algebra.FormallyUnramified k S := by
  letI iX : Algebra k[X] S := (Polynomial.aeval (R := k) x).toRingHom.toAlgebra
  haveI : IsScalarTower k k[X] S := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k S c = Polynomial.aeval x (algebraMap k k[X] c)
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  have halg : ∀ p : k[X], algebraMap k[X] S p = Polynomial.aeval x p := fun _ => rfl

  have hD : KaehlerDifferential.D k S x = 0 := by
    obtain ⟨r, s, hrs⟩ := hsep
    have h1 := (KaehlerDifferential.D k S).map_aeval g x
    rw [hg, map_zero] at h1
    have hunit : Polynomial.aeval x s * Polynomial.aeval x (Polynomial.derivative g) = 1 := by
      have := congrArg (Polynomial.aeval x) hrs
      rwa [map_add, map_mul, map_mul, hg, mul_zero, zero_add, map_one] at this
    calc KaehlerDifferential.D k S x = (Polynomial.aeval x s * Polynomial.aeval x (Polynomial.derivative g)) •
          KaehlerDifferential.D k S x := by rw [hunit, one_smul]
      _ = 0 := by rw [mul_smul, ← h1, smul_zero]

  refine ⟨⟨fun ω₁ ω₂ => ?_⟩⟩
  suffices h : ∀ ω : Ω[S⁄k], ω = 0 by rw [h ω₁, h ω₂]
  intro ω
  have hker : ω ∈ LinearMap.ker (KaehlerDifferential.map k k[X] S S) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  rw [← KaehlerDifferential.range_mapBaseChange k k[X] S] at hker
  obtain ⟨τ, rfl⟩ := hker
  induction τ using TensorProduct.induction_on with
  | zero => exact map_zero _
  | add a b ha hb => rw [map_add, ha, hb, add_zero]
  | tmul s ω₀ =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    suffices h0 : KaehlerDifferential.map k k k[X] S ω₀ = 0 by rw [h0, smul_zero]
    have hmem : ω₀ ∈ Submodule.span k[X] (Set.range (KaehlerDifferential.D k k[X])) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hmem using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      rw [KaehlerDifferential.map_D, halg, (KaehlerDifferential.D k S).map_aeval, hD, smul_zero]
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul r y _ hy => rw [LinearMap.map_smul_of_tower, hy, smul_zero]

include hθ in

private theorem exists_forall_formallyUnramified (u : A) {m : ℤ} (hm : MonicAt (θ u) m) (hm0 : m < 0) (hmq : -m < q)
    (hft : Algebra.FiniteType k B)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin k ({coord P u} : Set E)) E) :
    ∃ c : k[X], c ≠ 0 ∧ ∀ g : k[X], g.Separable → IsCoprime g c →
      Algebra.FormallyUnramified k (B ⧸ Ideal.span {Polynomial.aeval (Ideal.Quotient.mk P u) g}) := by
  classical
  set ub : B := Ideal.Quotient.mk P u with hub
  have htub : algebraMap B E ub = coord P u := rfl
  clear_value ub

  letI iB : Algebra k[X] B := (Polynomial.aeval (R := k) ub).toRingHom.toAlgebra
  haveI tkB : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k B c = Polynomial.aeval ub (algebraMap k k[X] c)
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI tkE : IsScalarTower k k[X] E := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k B E, IsScalarTower.algebraMap_apply k k[X] B,
      ← IsScalarTower.algebraMap_apply k[X] B E]
  have halgE : ∀ f : k[X], algebraMap k[X] E f = Polynomial.aeval (coord P u) f := fun f => by
    rw [IsScalarTower.algebraMap_apply k[X] B E, ← htub, Polynomial.aeval_algebraMap_apply]
    rfl

  set t : E := coord P u with ht
  letI iKt : Algebra k[X] (IntermediateField.adjoin k ({t} : Set E)) :=
    (Polynomial.aeval (IntermediateField.AdjoinSimple.gen k t)).toRingHom.toAlgebra
  haveI tKE : IsScalarTower k[X] (IntermediateField.adjoin k ({t} : Set E)) E := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgE]
    change Polynomial.aeval t f =
      ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen k t) f : IntermediateField.adjoin k ({t} : Set E)) : E)
    exact Polynomial.aeval_algHom_apply (IntermediateField.adjoin k ({t} : Set E)).val (IntermediateField.AdjoinSimple.gen k t) f
  haveI : IsFractionRing k[X] (IntermediateField.adjoin k ({t} : Set E)) :=
    isFractionRing_polynomial_adjoin t (transcendental_coord P θ hθ u hm hm0)
  haveI : Algebra.FormallyUnramified k[X] (IntermediateField.adjoin k ({t} : Set E)) :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors k[X])
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin k ({t} : Set E)) E := halg
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set E)) E := isSeparable_coord P θ hθ u hm hm0 hmq
  haveI : Algebra.FormallyUnramified (IntermediateField.adjoin k ({t} : Set E)) E :=
    Algebra.FormallyUnramified.of_isSeparable _ E
  haveI : Algebra.FormallyUnramified k[X] E := Algebra.FormallyUnramified.comp k[X] (IntermediateField.adjoin k ({t} : Set E)) E

  haveI : Algebra.FiniteType k B := hft
  haveI : Algebra.FiniteType k[X] B := Algebra.FiniteType.of_restrictScalars_finiteType k k[X] B

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_smul_kaehler_eq_zero (R := k[X]) (A := B) E
  have haalg : IsAlgebraic k[X] a := by
    have h1 : IsAlgebraic (IntermediateField.adjoin k ({t} : Set E)) (algebraMap B E a) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic k[X] (algebraMap B E a) :=
      (IsFractionRing.isAlgebraic_iff k[X] (IntermediateField.adjoin k ({t} : Set E)) E).mpr h1
    exact (isAlgebraic_algebraMap_iff (IsFractionRing.injective B E)).mp h2
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_algebraMap_mem_span ha0 haalg
  refine ⟨c, hc0, fun g hsep hcop => ?_⟩

  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {Polynomial.aeval ub g}) a) := by
    obtain ⟨r, s, hrs⟩ := hcop
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hc
    have h1 : Polynomial.aeval ub r * Polynomial.aeval ub g + Polynomial.aeval ub s * (b * a) = 1 := by
      rw [hb]
      change _ + _ * Polynomial.aeval ub c = 1
      rw [← map_mul, ← map_mul, ← map_add, hrs, map_one]
    have h2 : Ideal.Quotient.mk (Ideal.span {Polynomial.aeval ub g}) (Polynomial.aeval ub s * b) *
        Ideal.Quotient.mk (Ideal.span {Polynomial.aeval ub g}) a = 1 := by
      rw [← map_mul, mul_assoc, ← map_one (Ideal.Quotient.mk (Ideal.span {Polynomial.aeval ub g})), ← h1, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)), zero_add]
    exact isUnit_iff_exists_inv'.mpr ⟨_, h2⟩
  haveI hKX : Algebra.FormallyUnramified k[X] (B ⧸ Ideal.span {Polynomial.aeval ub g}) :=
    formallyUnramified_quotient_of_forall_smul_eq_zero ha _ hunit

  have hx : Polynomial.aeval (Ideal.Quotient.mk (Ideal.span {Polynomial.aeval ub g}) ub) g = 0 := by
    rw [← Ideal.Quotient.mkₐ_eq_mk k (Ideal.span {Polynomial.aeval ub g}), Polynomial.aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hinst : (Polynomial.aeval (R := k) (Ideal.Quotient.mk (Ideal.span {Polynomial.aeval ub g}) ub)).toRingHom.toAlgebra =
      (Ideal.Quotient.algebra k[X] : Algebra k[X] (B ⧸ Ideal.span {Polynomial.aeval ub g})) := by
    apply Algebra.algebra_ext
    intro p
    change Polynomial.aeval (Ideal.Quotient.mk _ ub) p = Ideal.Quotient.mk _ (Polynomial.aeval ub p)
    rw [← Ideal.Quotient.mkₐ_eq_mk k (Ideal.span {Polynomial.aeval ub g}), Polynomial.aeval_algHom_apply]
  exact formallyUnramified_of_polynomial (Ideal.Quotient.mk _ ub) (hX := by rw [hinst]; exact hKX) g hsep hx

end Unram

section Transport

variable {q : ℕ} [Fact q.Prime]
variable {A : Type} [CommRing A] (P : Ideal A) [P.IsPrime]
variable [Algebra (ZMod q) (A ⧸ P)]

set_option quotPrecheck false in
local notation "k" => ZMod q

omit [P.IsPrime] in
private theorem aeval_mk_map (u : A) (h : ℤ[X]) :
    Polynomial.aeval (Ideal.Quotient.mk P u) (h.map (Int.castRingHom k)) = Ideal.Quotient.mk P (Polynomial.aeval u h) := by
  have key : (Polynomial.aeval (Ideal.Quotient.mk P u)).toRingHom.comp (Polynomial.mapRingHom (Int.castRingHom k)) =
      (Ideal.Quotient.mk P).comp (Polynomial.aeval u).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.aeval (Ideal.Quotient.mk P u) ((Polynomial.C a).map (Int.castRingHom k)) =
        Ideal.Quotient.mk P (Polynomial.aeval u (Polynomial.C a))
      rw [Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C, eq_intCast, map_intCast, algebraMap_int_eq,
        eq_intCast, map_intCast]
    · change Polynomial.aeval (Ideal.Quotient.mk P u) ((Polynomial.X).map (Int.castRingHom k)) =
        Ideal.Quotient.mk P (Polynomial.aeval u Polynomial.X)
      rw [Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]
  exact RingHom.congr_fun key h

omit [P.IsPrime] in

private theorem transport (x : A) (y : A ⧸ P) (hxy : Ideal.Quotient.mk P x = y) (hnu : ¬ IsUnit y)
    (hfu : Algebra.FormallyUnramified k ((A ⧸ P) ⧸ Ideal.span {y})) :
    Nontrivial (A ⧸ (P ⊔ Ideal.span {x})) ∧ Algebra.FormallyUnramified ℤ (A ⧸ (P ⊔ Ideal.span {x})) := by
  have hideal : (Ideal.span {x}).map (Ideal.Quotient.mk P) = Ideal.span {y} := by
    rw [Ideal.map_span, Set.image_singleton, hxy]
  let e : (A ⧸ P) ⧸ Ideal.span {y} ≃+* A ⧸ (P ⊔ Ideal.span {x}) :=
    (Ideal.quotEquivOfEq hideal.symm).trans (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {x}))
  constructor
  · haveI : Nontrivial ((A ⧸ P) ⧸ Ideal.span {y}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, Ideal.span_singleton_eq_top]; exact hnu)
    exact e.toEquiv.symm.nontrivial
  · haveI := hfu
    haveI : @IsScalarTower ℤ k ((A ⧸ P) ⧸ Ideal.span {y}) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun n => by rw [eq_intCast, eq_intCast, map_intCast]
    haveI : Algebra.FormallyUnramified ℤ k :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ k) (ZMod.intCast_surjective)
    haveI : Algebra.FormallyUnramified ℤ ((A ⧸ P) ⧸ Ideal.span {y}) := Algebra.FormallyUnramified.comp ℤ k _
    exact Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun n => by simp))

variable {R : Type} [CommRing R] [Algebra R A] [Algebra R[X] A] [IsScalarTower R R[X] A]

private theorem isAlgebraic_adjoin_of_isIntegral (hint : Algebra.IsIntegral R[X] A)
    (hconst : ∀ c : R, algebraMap R (A ⧸ P) c ∈ Set.range (algebraMap k (A ⧸ P))) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin k ({coord P (algebraMap R[X] A Polynomial.X)} : Set (FractionRing (A ⧸ P))))
      (FractionRing (A ⧸ P)) := by
  classical
  haveI : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  let ψ : A →+* FractionRing (A ⧸ P) := algebraMap A (FractionRing (A ⧸ P))
  have hψ : ∀ a : A, ψ a = algebraMap (A ⧸ P) (FractionRing (A ⧸ P)) (Ideal.Quotient.mk P a) := fun a =>
    IsScalarTower.algebraMap_apply A (A ⧸ P) (FractionRing (A ⧸ P)) a
  let jE : FractionRing (A ⧸ P) := coord P (algebraMap R[X] A Polynomial.X)
  have hjE : ψ (algebraMap R[X] A Polynomial.X) = jE := hψ _
  let Kj : IntermediateField k (FractionRing (A ⧸ P)) := IntermediateField.adjoin k ({jE} : Set (FractionRing (A ⧸ P)))

  have hmem : ∀ p : R[X], ψ (algebraMap R[X] A p) ∈ Kj := fun p => by
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ => rw [map_add, map_add]; exact add_mem h₁ h₂
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow, hjE,
        Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply R R[X] A]
      refine mul_mem ?_ (pow_mem (IntermediateField.mem_adjoin_simple_self k jE) n)
      obtain ⟨c', hc'⟩ := hconst c
      rw [hψ, show Ideal.Quotient.mk P (algebraMap R A c) = algebraMap R (A ⧸ P) c from rfl, ← hc',
        ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem Kj c'
  let φ : R[X] →+* Kj := (ψ.comp (algebraMap R[X] A)).codRestrict Kj.toSubring hmem
  have hcomp : (algebraMap Kj (FractionRing (A ⧸ P))).comp φ = ψ.comp (algebraMap R[X] A) := RingHom.ext fun _ => rfl
  have hintK : ∀ a : A, IsIntegral Kj (ψ a) := fun a => (hint.isIntegral a).map_of_comp_eq φ ψ hcomp
  refine ⟨fun e => ?_⟩
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ P) e
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : ψ a ∈ algebraicClosure Kj (FractionRing (A ⧸ P)) := (mem_algebraicClosure_iff).mpr (hintK a).isAlgebraic
  have ha' : ψ a' ∈ algebraicClosure Kj (FractionRing (A ⧸ P)) := (mem_algebraicClosure_iff).mpr (hintK a').isAlgebraic
  rw [hψ] at ha ha'
  exact (mem_algebraicClosure_iff).mp (div_mem ha ha')

end Transport

end ModularCurve.XHDRModelAtP.QFibreUnramH

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.jChartFin XHDRModelAtP translation_mem_GammaH qExpFunctionFieldC qExpand dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffMap_ofPowerSeries jqModC jqModC_rat coeffMap_qExpand deltaSeries modularUnitSeries isMonicOfOrder_modularUnitSeries modularUnitSeries_ne_zero coeffEmb_qExpand exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "iota0_spec w isIntegral π iota0 mk comp"
namespace QFibreUnramH
namespace C6Nontrivial
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

open scoped IntermediateField.algebraAdjoinAdjoin in

private theorem exists_forall_not_isUnit_aeval (k : Type) [Field k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
    (hfg : Algebra.FiniteType k B) (x : B) (hx : Transcendental k (algebraMap B (FractionRing B) x))
    (halg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin k {algebraMap B (FractionRing B) x}) (FractionRing B)) :
    ∃ f : k[X], f ≠ 0 ∧ ∀ g : k[X], 0 < g.natDegree → IsCoprime g f → ¬ IsUnit (Polynomial.aeval x g) := by
  classical

  obtain ⟨xE, hxE⟩ : ∃ xE : FractionRing B, xE = algebraMap B (FractionRing B) x := ⟨_, rfl⟩
  rw [← hxE] at hx halg
  have hinj : Function.Injective (Polynomial.aeval xE : k[X] →ₐ[k] FractionRing B) := transcendental_iff_injective.mp hx
  let R₀ : Subalgebra k (FractionRing B) := Algebra.adjoin k {xE}
  let e : k[X] ≃ₐ[k] ↥R₀ :=
    (AlgEquiv.ofInjective (Polynomial.aeval xE) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k xE).symm)
  have he : ∀ p : k[X], ((e p : ↥R₀) : FractionRing B) = Polynomial.aeval xE p := fun _ => rfl
  have he' : ∀ p : k[X], IsIntegral ↥R₀ (Polynomial.aeval xE p) := fun p => by
    rw [← he]; exact isIntegral_algebraMap (R := ↥R₀) (A := FractionRing B) (x := e p)

  have halgR : ∀ b : B, IsAlgebraic ↥R₀ (algebraMap B (FractionRing B) b) := fun b =>
    (IsFractionRing.isAlgebraic_iff ↥R₀ ↥(IntermediateField.adjoin k {xE}) (FractionRing B)).mpr
      (halg.isAlgebraic _)

  have hmult : ∀ b : B, ∃ p : k[X], p ≠ 0 ∧
      IsIntegral ↥R₀ (Polynomial.aeval xE p * algebraMap B (FractionRing B) b) := by
    intro b
    obtain ⟨y, hy0, hint⟩ := (halgR b).exists_integral_multiple
    refine ⟨e.symm y, fun h => hy0 (by rw [← e.apply_symm_apply y, h, map_zero]), ?_⟩
    rw [← he, e.apply_symm_apply]
    have hint' := hint
    rw [Algebra.smul_def] at hint'
    exact hint'
  choose p hp0 hpint using hmult

  obtain ⟨s, hs⟩ := hfg.out
  refine ⟨∏ b ∈ s, p b, Finset.prod_ne_zero_iff.mpr fun b _ => hp0 b, ?_⟩
  intro g hg hcop hunit
  obtain ⟨f, hf⟩ : ∃ f : k[X], f = ∏ b ∈ s, p b := ⟨_, rfl⟩
  rw [← hf] at hcop

  obtain ⟨π, hπ, hπg⟩ := Polynomial.exists_irreducible_of_natDegree_pos hg
  have hπf : ¬ π ∣ f := fun h => hπ.not_isUnit (hcop.isUnit_of_dvd' hπg h)

  obtain ⟨fE, hfEdef⟩ : ∃ fE : FractionRing B, fE = Polynomial.aeval xE f := ⟨_, rfl⟩
  have hfE : IsIntegral ↥R₀ fE := hfEdef ▸ he' f
  let D : Subalgebra k (FractionRing B) :=
    { carrier := {z | ∃ m : ℕ, IsIntegral ↥R₀ (fE ^ m * z)}
      mul_mem' := by
        rintro z w ⟨m, hm⟩ ⟨n, hn⟩
        exact ⟨m + n, by rw [pow_add, mul_mul_mul_comm]; exact hm.mul hn⟩
      one_mem' := ⟨0, by rw [pow_zero, mul_one]; exact isIntegral_one⟩
      add_mem' := by
        rintro z w ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have : fE ^ (m + n) * (z + w) = fE ^ n * (fE ^ m * z) + fE ^ m * (fE ^ n * w) := by ring
        rw [this]
        exact ((hfE.pow n).mul hm).add ((hfE.pow m).mul hn)
      zero_mem' := ⟨0, by rw [mul_zero]; exact isIntegral_zero⟩
      algebraMap_mem' := fun c => ⟨0, by
        rw [pow_zero, one_mul, IsScalarTower.algebraMap_apply k ↥R₀ (FractionRing B)]
        exact isIntegral_algebraMap⟩ }
  have hBD : ∀ b : B, algebraMap B (FractionRing B) b ∈ D := by
    have hgen : (Algebra.adjoin k (s : Set B)).map (IsScalarTower.toAlgHom k B (FractionRing B)) ≤ D := by
      rw [AlgHom.map_adjoin]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨1, ?_⟩
      rw [pow_one, IsScalarTower.coe_toAlgHom', hfEdef, hf, ← Finset.prod_erase_mul _ _ hb, map_mul, mul_assoc]
      exact (he' _).mul (hpint b)
    intro b
    exact hgen ⟨b, by rw [hs]; trivial, rfl⟩

  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  obtain ⟨m, hm⟩ := hBD u
  let c1 : ↥(integralClosure ↥R₀ (FractionRing B)) := ⟨fE ^ m * algebraMap B (FractionRing B) u, hm⟩
  let gC : ↥(integralClosure ↥R₀ (FractionRing B)) := ⟨Polynomial.aeval xE g, he' g⟩
  let fC : ↥(integralClosure ↥R₀ (FractionRing B)) := ⟨fE, hfE⟩
  have hrel : gC * c1 = fC ^ m := by
    apply Subtype.ext
    change Polynomial.aeval xE g * (fE ^ m * algebraMap B (FractionRing B) u) = fE ^ m
    have h1 : Polynomial.aeval xE g * algebraMap B (FractionRing B) u = 1 := by
      rw [hxE, Polynomial.aeval_algebraMap_apply, ← map_mul, hu, map_one]
    calc Polynomial.aeval xE g * (fE ^ m * algebraMap B (FractionRing B) u)
        = fE ^ m * (Polynomial.aeval xE g * algebraMap B (FractionRing B) u) := by ring
      _ = fE ^ m := by rw [h1, mul_one]

  haveI : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  haveI h𝔭 : (Ideal.map e (Ideal.span {π})).IsPrime := Ideal.map_isPrime_of_equiv e
  obtain ⟨𝔔, -, h𝔔, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := ↥(integralClosure ↥R₀ (FractionRing B)))
    (Ideal.map e (Ideal.span {π})) ⊥
    (Ideal.comap_bot_le_of_injective _ (fun a b hab => by
      apply Subtype.ext
      have := congrArg (fun z : ↥(integralClosure ↥R₀ (FractionRing B)) => (z : FractionRing B)) hab
      exact this))
  have hπ𝔔 : algebraMap ↥R₀ ↥(integralClosure ↥R₀ (FractionRing B)) (e π) ∈ 𝔔 := by
    rw [← Ideal.mem_comap, hcomap]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self π)
  have hgC : gC = algebraMap ↥R₀ ↥(integralClosure ↥R₀ (FractionRing B)) (e g) := Subtype.ext rfl
  have hg𝔔 : gC ∈ 𝔔 := by
    obtain ⟨r, hr⟩ := hπg
    rw [hgC, hr, map_mul, map_mul]
    exact 𝔔.mul_mem_right _ hπ𝔔
  have hf𝔔 : fC ∈ 𝔔 := h𝔔.mem_of_pow_mem m (by rw [← hrel]; exact 𝔔.mul_mem_right _ hg𝔔)
  have hfC : fC = algebraMap ↥R₀ ↥(integralClosure ↥R₀ (FractionRing B)) (e f) := by
    apply Subtype.ext
    change fE = _
    rw [hfEdef]
    rfl
  rw [hfC, ← Ideal.mem_comap, hcomap] at hf𝔔
  have hfπ : f ∈ Ideal.span {π} := by
    rw [← Ideal.comap_map_of_bijective e e.bijective (I := Ideal.span {π}), Ideal.mem_comap]
    exact hf𝔔
  exact hπf (Ideal.mem_span_singleton.mp hfπ)

private theorem exists_forall_not_isUnit_aeval_zmod {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] [IsDomain B]
    [Algebra (ZMod q) B] (hfg : Algebra.FiniteType (ZMod q) B) (x : B)
    (hx : Transcendental (ZMod q) (algebraMap B (FractionRing B) x))
    (halg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin (ZMod q) {algebraMap B (FractionRing B) x}) (FractionRing B)) :
    ∃ f : (ZMod q)[X], f ≠ 0 ∧ ∀ g : (ZMod q)[X], 0 < g.natDegree → IsCoprime g f → ¬ IsUnit (Polynomial.aeval x g) :=
  exists_forall_not_isUnit_aeval (ZMod q) B hfg x hx halg

end ModularCurve.XHDRModelAtP.QFibreUnramH.C6Nontrivial

namespace AVOIDHUnit

def deltaInt : LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.X * dedekindEtaUnit)

def deltaInvInt : LaurentSeries ℤ :=
  HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem deltaInt_eq : deltaInt = HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit := by
  rw [deltaInt, map_mul, HahnSeries.ofPowerSeries_X]

theorem deltaInt_mul_deltaInvInt : deltaInt * deltaInvInt = 1 := by
  rw [deltaInt_eq, deltaInvInt, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul,
    dedekindEtaUnit_mul_inv, map_one, mul_one]
  simp

variable (p : ℕ) [Fact p.Prime]

def unitInt : LaurentSeries ℤ := deltaInt * qExpand ℤ p deltaInvInt

def unitInvInt : LaurentSeries ℤ := deltaInvInt * qExpand ℤ p deltaInt

theorem unitInt_mul_unitInvInt : unitInt p * unitInvInt p = 1 := by
  rw [unitInt, unitInvInt, mul_mul_mul_comm, deltaInt_mul_deltaInvInt, ← map_mul,
    mul_comm deltaInvInt, deltaInt_mul_deltaInvInt, map_one, mul_one]

section CoeffMap

variable {K : Type*} [CommRing K]

theorem coeffMap_deltaInt (f : ℤ →+* K) :
    coeffMap f deltaInt =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) := by
  rw [deltaInt, coeffMap_ofPowerSeries]

theorem coeffMap_deltaInt_mul_deltaInvInt (f : ℤ →+* K) :
    coeffMap f deltaInt * coeffMap f deltaInvInt = 1 := by
  rw [← map_mul, deltaInt_mul_deltaInvInt, map_one]

theorem coeffMap_unitInt (f : ℤ →+* K) :
    coeffMap f (unitInt p) = coeffMap f deltaInt * qExpand K p (coeffMap f deltaInvInt) := by
  rw [unitInt, map_mul, ModularCurve.coeffMap_qExpand]

theorem coeffMap_unitInvInt (f : ℤ →+* K) :
    coeffMap f (unitInvInt p) = coeffMap f deltaInvInt * qExpand K p (coeffMap f deltaInt) := by
  rw [unitInvInt, map_mul, ModularCurve.coeffMap_qExpand]

theorem coeffMap_unitInt_mul_unitInvInt (f : ℤ →+* K) :
    coeffMap f (unitInt p) * coeffMap f (unitInvInt p) = 1 := by
  rw [← map_mul, unitInt_mul_unitInvInt, map_one]

theorem isUnit_coeffMap_unitInt (f : ℤ →+* K) : IsUnit (coeffMap f (unitInt p)) :=
  IsUnit.of_mul_eq_one _ (coeffMap_unitInt_mul_unitInvInt p f)

theorem isUnit_coeffMap_unitInvInt (f : ℤ →+* K) : IsUnit (coeffMap f (unitInvInt p)) :=
  IsUnit.of_mul_eq_one_right _ (coeffMap_unitInt_mul_unitInvInt p f)

theorem coeffMap_unitInt_ne_zero [Nontrivial K] (f : ℤ →+* K) : coeffMap f (unitInt p) ≠ 0 :=
  (isUnit_coeffMap_unitInt p f).ne_zero

theorem coeffMap_unitInvInt_ne_zero [Nontrivial K] (f : ℤ →+* K) : coeffMap f (unitInvInt p) ≠ 0 :=
  (isUnit_coeffMap_unitInvInt p f).ne_zero

end CoeffMap

theorem coeffMap_rat_deltaInt : coeffMap (Int.castRingHom ℚ) deltaInt = deltaSeries := by
  rw [deltaInt_eq, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  rfl

theorem coeffMap_rat_deltaInvInt : coeffMap (Int.castRingHom ℚ) deltaInvInt = deltaSeries⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← coeffMap_rat_deltaInt, coeffMap_deltaInt_mul_deltaInvInt]

theorem coeffMap_rat_unitInt : coeffMap (Int.castRingHom ℚ) (unitInt p) = modularUnitSeries p := by
  rw [coeffMap_unitInt, coeffMap_rat_deltaInt, coeffMap_rat_deltaInvInt, map_inv₀]
  rfl

theorem coeffMap_rat_unitInvInt :
    coeffMap (Int.castRingHom ℚ) (unitInvInt p) = (modularUnitSeries p)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← coeffMap_rat_unitInt, coeffMap_unitInt_mul_unitInvInt]

end AVOIDHUnit

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.jChartFin XHDRModelAtP translation_mem_GammaH qExpFunctionFieldC qExpand dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffMap_ofPowerSeries jqModC jqModC_rat coeffMap_qExpand deltaSeries modularUnitSeries isMonicOfOrder_modularUnitSeries modularUnitSeries_ne_zero coeffEmb_qExpand exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "iota0_spec w isIntegral π iota0 mk comp"
namespace QFibreUnramH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

section DictionaryH

open scoped MatrixGroups

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

set_option quotPrecheck false in
local notation "𝒜" => (↥(chartAlgFin p (ΓM M H) hj) : Type)
set_option quotPrecheck false in
local notation "FM" => (↥(qExpFunctionFieldC ℚ (ΓM M H)) : Type)

private theorem monicAt_coeffMap_unitInt :
    MonicAt (coeffMap (Int.castRingHom (ZMod p)) (AVOIDHUnit.unitInt p)) (1 - p) := by
  have hxc : ∀ i : ℤ, (((AVOIDHUnit.unitInt p).coeff i : ℤ) : ℚ) = (modularUnitSeries p).coeff i := fun i => by
    rw [← AVOIDHUnit.coeffMap_rat_unitInt, ModularCurve.coeffMap_coeff]; rfl
  have hmono := ModularCurve.isMonicOfOrder_modularUnitSeries p
  refine MonicAt.of_coeff ?_ fun i hi => ?_
  · rw [ModularCurve.coeffMap_coeff]
    have := hxc (1 - p); rw [hmono.coeff_self] at this
    have hx1 : (AVOIDHUnit.unitInt p).coeff (1 - p) = 1 := by exact_mod_cast this
    rw [hx1, map_one]
  · rw [ModularCurve.coeffMap_coeff]
    have := hxc i; rw [hmono.coeff_of_lt hi] at this
    have hx0 : (AVOIDHUnit.unitInt p).coeff i = 0 := by exact_mod_cast this
    rw [hx0, map_zero]

include hpM2 hHp 𝔛 in

private theorem exists_theta_H (v : 𝒜)
    (hv : ((v : FM) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : FM) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹)
    (P : Ideal 𝒜) [P.IsPrime] (hP : P ∈ (Ideal.span {((p : ℕ) : 𝒜)}).minimalPrimes) (hvP : v ∉ P) :
    ∃ θ : 𝒜 →+* LaurentSeries (ZMod p), RingHom.ker θ = P ∧ MonicAt (θ v) (1 - p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨σ, hσ, -⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp

  obtain ⟨v₀, w₀, hv₀, hw₀, hvw, hσv⟩ := ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj σ hσ

  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) hp
  have hRext : ∀ (g₁ g₂ : R p →+* FM), g₁ = g₂ := fun g₁ g₂ =>
    IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)
  have hcomm : ∀ r : R p, σ (algebraMap (R p) FM r) = algebraMap (R p) FM r := fun r =>
    RingHom.congr_fun (hRext (σ.toRingEquiv.toRingHom.comp (algebraMap (R p) FM)) (algebraMap (R p) FM)) r

  let σ' : @AlgEquiv ℚ FM FM _ _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H)))
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) :=
    @AlgEquiv.ofRingEquiv ℚ FM FM _ _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H)))
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) σ.toRingEquiv (fun r => by
        have h1 : @algebraMap ℚ FM _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) r = (r : FM) :=
          eq_ratCast _ r
        rw [h1]
        exact map_ratCast σ.toRingEquiv r)
  have hσ'σ : ∀ f : FM, σ' f = σ f := fun _ => rfl

  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : @IsScalarTower (R p) ℚ FM _ (@Algebra.toSMul ℚ FM _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H)))) _ :=
    @IsScalarTower.of_algebraMap_eq (R p) ℚ FM _ _ _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H))) _
      (fun r => (RingHom.congr_fun (hRext (algebraMap (R p) FM)
        ((@algebraMap ℚ FM _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (ΓM M H)))).comp (algebraMap (R p) ℚ))) r))
  have hAp : ((p : ℕ) : R p) ∈ IsLocalRing.maximalIdeal (R p) := by
    rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp]; exact Ideal.mem_span_singleton_self _
  have hjcoe : ((jAt (ΓM M H) hj : FM) : LaurentSeries ℚ) = coeffEmb ℚ jq := by
    ext k; rw [coeffEmb_coeff, eq_ratCast, Rat.cast_id, coe_jAt, jqModC_rat]
  have hσj : ((σ' (jAt (ΓM M H) hj) : FM) : LaurentSeries ℚ) = coeffEmb ℚ (qExpand ℚ p jq) := by
    rw [hσ'σ, coeffEmb_qExpand, ← hjcoe]
    exact hσ (jAt (ΓM M H) hj) (jAt (ΓN p M H hpM) hj) rfl
  obtain ⟨hstab, -⟩ := ModularCurve.chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand p ℚ
    (qExpFunctionFieldC ℚ (ΓM M H)) (R p) hAp (jAt (ΓM M H) hj) hjcoe σ' hσj
  have hstab' : ∀ b : FM, b ∈ chartAlgFin p (ΓM M H) hj ↔ σ.symm b ∈ chartAlgFin p (ΓM M H) hj := fun b => by
    rw [hstab (σ.symm b), hσ'σ, AlgEquiv.apply_symm_apply]
  let theta : 𝒜 ≃ₐ[R p] 𝒜 :=
    { toFun := fun b => ⟨σ b, (hσ'σ (b : FM)) ▸ (hstab b).mp b.2⟩
      invFun := fun b => ⟨σ.symm b, (hstab' b).mp b.2⟩
      left_inv := fun b => Subtype.ext (σ.symm_apply_apply _)
      right_inv := fun b => Subtype.ext (σ.apply_symm_apply _)
      map_mul' := fun a b => Subtype.ext (by simp only [Subalgebra.coe_mul]; exact map_mul σ _ _)
      map_add' := fun a b => Subtype.ext (by simp only [Subalgebra.coe_add]; exact map_add σ _ _)
      commutes' := fun r => Subtype.ext (hcomm r) }
  have htheta_coe : ∀ b : 𝒜, ((theta b : 𝒜) : FM) = σ (b : FM) := fun _ => rfl
  have htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (𝔛.iota0 b) : 𝒜) : FM) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) :=
    fun b => by rw [htheta_coe]; exact hσ _ _ (𝔛.iota0_spec b)

  obtain ⟨θ, hθ1, hθ2, hker_ne, hmin, -, -⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj
      𝔛.iota0 𝔛.iota0_spec theta htheta

  have hres : (GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom (R p)) = Int.castRingHom (ZMod p) :=
    RingHom.ext_int _ _
  have hθv₀ : θ 0 v₀ = coeffMap (Int.castRingHom (ZMod p)) (AVOIDHUnit.unitInt p) := by
    have h := hθ2 v₀ (coeffMap (Int.castRingHom (R p)) (AVOIDHUnit.unitInt p)) (by
      rw [coeffMap_coeffMap, RingHom.ext_int ((algebraMap (R p) ℚ).comp (Int.castRingHom (R p))) (Int.castRingHom ℚ),
        AVOIDHUnit.coeffMap_rat_unitInt, hv₀])
    rw [h, coeffMap_coeffMap, hres]
  have hmono : MonicAt (θ 0 v₀) (1 - p) := by rw [hθv₀]; exact monicAt_coeffMap_unitInt p

  have hpker : ∀ i, ((p : ℕ) : 𝒜) ∈ RingHom.ker (θ i) := fun i => by
    have hm : RingHom.ker (θ i) ∈ (Ideal.span {((p : ℕ) : 𝒜)}).minimalPrimes := by
      rw [hmin]; fin_cases i <;> simp
    exact hm.1.2 (Ideal.subset_span rfl)
  have hθw₀ : θ 0 w₀ = 0 := by
    have h := congrArg (θ 0) hvw
    rw [map_mul, map_pow, map_natCast (algebraMap (R p) 𝒜), map_pow, (RingHom.mem_ker).mp (hpker 0),
      zero_pow (by norm_num)] at h
    exact (mul_eq_zero.mp h).resolve_left hmono.ne_zero

  have hthv : theta v₀ = w₀ := Subtype.ext hσv
  have hw₀0 : (w₀ : FM) ≠ 0 := by
    intro h0
    have := congrArg (fun x : FM => (x : LaurentSeries ℚ)) h0
    simp only [hw₀, ZeroMemClass.coe_zero] at this
    have hpL : (p : LaurentSeries ℚ) ≠ 0 := by
      rw [← map_natCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) p, Ne, map_eq_zero_iff _ HahnSeries.C_injective]
      exact_mod_cast hp.ne_zero
    exact (mul_ne_zero (pow_ne_zero _ hpL) (inv_ne_zero (modularUnitSeries_ne_zero p))) this
  have hthw : theta w₀ = v₀ := by
    apply Subtype.ext
    rw [htheta_coe]

    have h1 : σ (v₀ : FM) * σ (w₀ : FM) = (v₀ : FM) * (w₀ : FM) := by
      rw [← map_mul, ← Subalgebra.coe_mul, hvw, Subalgebra.coe_algebraMap, hcomm]
    rw [hσv] at h1
    exact mul_left_cancel₀ hw₀0 (h1.trans (mul_comm _ _))
  have hθ1v₀ : θ 1 v₀ = 0 := by rw [hθ1, hthv, hθw₀]
  have hθ1w₀ : θ 1 w₀ = θ 0 v₀ := by rw [hθ1, hthw]

  have hPmem : P ∈ ({RingHom.ker (θ 0), RingHom.ker (θ 1)} : Set (Ideal 𝒜)) := hmin ▸ hP
  rcases hv with hv | hv
  ·
    have hvv : v = v₀ := Subtype.ext (Subtype.ext (hv.trans hv₀.symm))
    subst hvv
    rcases hPmem with h | h
    · exact ⟨θ 0, h.symm, hmono⟩
    · exact absurd ((RingHom.mem_ker).mpr hθ1v₀) (h ▸ hvP)
  ·
    have hvv : v = w₀ := Subtype.ext (Subtype.ext (hv.trans hw₀.symm))
    subst hvv
    rcases hPmem with h | h
    · exact absurd ((RingHom.mem_ker).mpr hθw₀) (h ▸ hvP)
    · exact ⟨θ 1, h.symm, hθ1w₀ ▸ hmono⟩

private theorem natCast_mem_H (P : Ideal 𝒜) (hP : P ∈ (Ideal.span {((p : ℕ) : 𝒜)}).minimalPrimes) :
    ((p : ℕ) : 𝒜) ∈ P :=
  hP.1.2 (Ideal.subset_span rfl)

end DictionaryH

section Modular

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

set_option quotPrecheck false in
local notation "F" => (↥(qExpFunctionFieldC ℚ (ΓM M H)) : Type)
set_option quotPrecheck false in
local notation "𝒜" => (↥(chartAlgFin p (ΓM M H) hj) : Type)
set_option quotPrecheck false in
local notation "ℤq" => (R p : Type)
set_option quotPrecheck false in
local notation "k" => ZMod p

variable (P : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [P.IsPrime]
  [Algebra (ZMod p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ P)]

private theorem algebraMap_ratLocalizedAt_mem_range (c : ℤq) :
    algebraMap ℤq (𝒜 ⧸ P) c ∈ Set.range (algebraMap k (𝒜 ⧸ P)) := by
  haveI : Nontrivial (𝒜 ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hp : p.Prime := Fact.out
  set r : ℚ := (c : ℚ) with hr
  have hden : r.den.Coprime p := by
    have : r ∈ GaloisRep.ratLocalizedAt p := c.2
    exact this
  have hdenk : ((r.den : ℕ) : k) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.mp hden) h
    exact hp.one_lt.ne' this

  have hA : algebraMap ℤq 𝒜 c * ((r.den : ℕ) : 𝒜) = ((r.num : ℤ) : 𝒜) := by
    have hinjv : Function.Injective (chartAlgFin p (ΓM M H) hj).val := Subtype.val_injective
    apply hinjv
    rw [map_mul, map_natCast, map_intCast, AlgHom.commutes]

    haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
    haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) hp
    have hRF : algebraMap ℤq F = (Rat.castHom F).comp (GaloisRep.ratLocalizedAt p).subtype :=
      IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)
    rw [hRF, RingHom.comp_apply, Rat.coe_castHom, Subring.coe_subtype]
    change ((r : ℚ) : F) * _ = _
    rw [← Rat.cast_natCast, ← Rat.cast_intCast, ← Rat.cast_mul, Rat.mul_den_eq_num]
  have hB : algebraMap ℤq (𝒜 ⧸ P) c * algebraMap k (𝒜 ⧸ P) (r.den : ℕ) = algebraMap k (𝒜 ⧸ P) (r.num : ℤ) := by
    have h0 : algebraMap ℤq (𝒜 ⧸ P) c = Ideal.Quotient.mk P (algebraMap ℤq 𝒜 c) := rfl
    rw [map_natCast, map_intCast, h0, ← map_natCast (Ideal.Quotient.mk P), ← map_mul, hA, map_intCast]
  refine ⟨(r.num : ℤ) * ((r.den : ℕ) : k)⁻¹, ?_⟩
  have hinj : Function.Injective (algebraMap k (𝒜 ⧸ P)) := (algebraMap k (𝒜 ⧸ P)).injective
  haveI : IsDomain (𝒜 ⧸ P) := Ideal.Quotient.isDomain P
  have hne : algebraMap k (𝒜 ⧸ P) (r.den : ℕ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hdenk
  apply mul_right_cancel₀ hne
  rw [← map_mul, mul_assoc, inv_mul_cancel₀ hdenk, mul_one, hB]

private theorem finiteType_quotient : Algebra.FiniteType k (𝒜 ⧸ P) := by
  classical
  haveI : Algebra.FiniteType ℤq 𝒜 :=
    (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H)
      (translation_mem_GammaH M H) (jAt (ΓM M H) hj) (coe_jAt _ _)).1
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := ℤq) (A := 𝒜)
  refine ⟨⟨S.image (Ideal.Quotient.mk P), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro b -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a ∈ Algebra.adjoin ℤq (S : Set 𝒜) := by rw [hS]; exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  | algebraMap c =>
    obtain ⟨c', hc'⟩ := algebraMap_ratLocalizedAt_mem_range P c
    have h0 : Ideal.Quotient.mk P (algebraMap ℤq 𝒜 c) = algebraMap ℤq (𝒜 ⧸ P) c := rfl
    rw [h0, ← hc']
    exact Subalgebra.algebraMap_mem _ c'
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem isIntegral_polynomial_chartAlgFin :
    letI := (Polynomial.aeval (R := ℤq) (XHDRLevel.jChartFin p (ΓM M H) hj)).toRingHom.toAlgebra
    Algebra.IsIntegral ℤq[X] 𝒜 := by
  letI iXA : Algebra ℤq[X] 𝒜 := (Polynomial.aeval (R := ℤq) (XHDRLevel.jChartFin p (ΓM M H) hj)).toRingHom.toAlgebra
  letI iXF : Algebra ℤq[X] F := (Polynomial.aeval (R := ℤq) ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))))).toRingHom.toAlgebra

  let f : ℤq[X] →+* ↥(Algebra.adjoin ℤq ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set F)) :=
    (Polynomial.aeval (R := ℤq) ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))))).toRingHom.codRestrict (Algebra.adjoin ℤq ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set F)).toSubring
      fun pol => Polynomial.aeval_mem_adjoin_singleton ℤq _
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨pol, rfl⟩ := hy
    exact ⟨pol, rfl⟩
  have hval : ∀ pol : ℤq[X], ((f pol : ↥(Algebra.adjoin ℤq ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set F))) : F) = algebraMap ℤq[X] F pol := fun _ => rfl
  refine ⟨fun a => ?_⟩

  have h1 : IsIntegral ↥(Algebra.adjoin ℤq ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set F)) (a : F) := (TwoChartIntegralModel.mem_chartAlg_iff (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))).mp a.2
  have h2 : IsIntegral ℤq[X] (a : F) := by
    obtain ⟨pol, hpmon, hpev⟩ := h1
    have hlifts : pol ∈ Polynomial.lifts f := (Polynomial.lifts_iff_coeff_lifts pol).mpr fun i => hf _
    obtain ⟨p', hp'p, -, hp'mon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hpmon
    refine ⟨p', hp'mon, ?_⟩
    have : algebraMap ℤq[X] F = (algebraMap ↥(Algebra.adjoin ℤq ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set F)) F).comp f :=
      RingHom.ext fun pol => (hval pol).symm
    rw [this, ← Polynomial.eval₂_map, hp'p]
    exact hpev

  let val : 𝒜 →ₐ[ℤq[X]] F :=
    { (chartAlgFin p (ΓM M H) hj).val.toRingHom with
      commutes' := fun pol => by
        change (chartAlgFin p (ΓM M H) hj).val (Polynomial.aeval (XHDRLevel.jChartFin p (ΓM M H) hj) pol) =
          Polynomial.aeval ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) pol
        rw [← Polynomial.aeval_algHom_apply]; rfl }
  exact (isIntegral_algHom_iff val Subtype.val_injective).mp h2

end Modular

end ModularCurve.XHDRModelAtP.QFibreUnramH

open ModularCurve.XHDRModelAtP.QFibreUnramH in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹)
    (P : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [P.IsPrime]
    (hP : P ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes) (hvP : v ∉ P) :
    ∃ avoid : (ZMod p)[X], avoid ≠ 0 ∧
      ∀ h : ℤ[X], 0 < (h.map (Int.castRingHom (ZMod p))).natDegree → (h.map (Int.castRingHom (ZMod p))).Separable →
        IsCoprime (h.map (Int.castRingHom (ZMod p))) avoid →
        Nontrivial (↥(chartAlgFin p (ΓM M H) hj) ⧸ (P ⊔ Ideal.span {Polynomial.aeval v h})) ∧
        Algebra.FormallyUnramified ℤ
          (↥(chartAlgFin p (ΓM M H) hj) ⧸ (P ⊔ Ideal.span {Polynomial.aeval v h})) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨θ, hθ, hmono⟩ := exists_theta_H p M H hpM hpM2 hHp hj 𝔛 v hv P hP hvP
  have hqP := natCast_mem_H p M H hj P hP
  letI : Algebra (ZMod p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ P) := algebraK P hqP
  haveI : IsDomain (↥(chartAlgFin p (ΓM M H) hj) ⧸ P) := Ideal.Quotient.isDomain P
  have hm0 : (1 - (p : ℤ)) < 0 := by have := hp.two_le; omega
  have hmq : -(1 - (p : ℤ)) < p := by omega
  have hft := finiteType_quotient P
  have htr := transcendental_coord P θ hθ v hmono hm0

  letI iXA : Algebra ((R p))[X] ↥(chartAlgFin p (ΓM M H) hj) :=
    (Polynomial.aeval (R := (R p)) (XHDRLevel.jChartFin p (ΓM M H) hj)).toRingHom.toAlgebra
  haveI : IsScalarTower (R p) ((R p))[X] ↥(chartAlgFin p (ΓM M H) hj) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap _ _ c = Polynomial.aeval (XHDRLevel.jChartFin p (ΓM M H) hj) (algebraMap _ _ c)
      rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI := isAlgebraic_adjoin_of_isIntegral P isIntegral_polynomial_chartAlgFin (algebraMap_ratLocalizedAt_mem_range P)
  have halg := isAlgebraic_adjoin_of_transcendental
    (coord P (algebraMap ((R p))[X] ↥(chartAlgFin p (ΓM M H) hj) Polynomial.X))
    (coord P v) htr

  obtain ⟨c, hc0, hc⟩ := exists_forall_formallyUnramified P θ hθ v hmono hm0 hmq hft halg
  obtain ⟨f, hf0, hf⟩ := C6Nontrivial.exists_forall_not_isUnit_aeval_zmod hft (Ideal.Quotient.mk P v) htr halg
  refine ⟨c * f, mul_ne_zero hc0 hf0, fun h hdeg hsep hcop => ?_⟩
  exact transport P (Polynomial.aeval v h) _ (aeval_mk_map P v h).symm (hf _ hdeg hcop.of_mul_right_right)
    (hc _ hsep hcop.of_mul_right_left)

#print axioms solution

end

end S_ModularCurve_XHDRModelAtP_exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin (solution)
