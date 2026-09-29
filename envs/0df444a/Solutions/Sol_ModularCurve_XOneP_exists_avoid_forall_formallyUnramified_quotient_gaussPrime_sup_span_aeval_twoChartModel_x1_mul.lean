-- Prove2me | solution 1 for ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fcd5c68a-7da3-53e4-87cc-f304bfdd5ff3

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_XOneP_exists_gaussValuationSubring_x1_mul
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "TwoChart.mem_chartAlg_iff TwoChart.chartAlgFin TwoChart.jChartFin x1FunctionField jq modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange modularUnitSeries coeff_modularUnitSeries_self coeff_modularUnitSeries_of_lt XOneP.exists_gaussValuationSubring_x1_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd modularUnitSeries_mem_valuationSubring_pair_of_not_dvd modularUnitSeries_mem_modularFunctionFieldFull"
namespace XOneP
p2m_export "ModularCurve.XOneP" "exists_gaussValuationSubring_x1_mul"
namespace UnrSpecZero
p2m_open "ModularCurve.XOneP ModularCurve~coeffMap_ofPowerSeries"

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

section LaurentHelpers

private theorem coeff_ofPowerSeries_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R f).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  intro h
  simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
  obtain ⟨m, hm⟩ := h
  change (m : ℤ) = _ at hm
  omega

private theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : PowerSeries R) :
    ModularCurve.coeffMap φ (HahnSeries.ofPowerSeries ℤ R f) = HahnSeries.ofPowerSeries ℤ S (f.map φ) := by
  ext n
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [coeff_ofPowerSeries_of_neg f hn, coeff_ofPowerSeries_of_neg _ hn, map_zero]

private theorem coeff_ofPowerSeries_mul_single_add {R : Type*} [CommRing R] (f : PowerSeries R) (a b : ℤ) :
    (HahnSeries.ofPowerSeries ℤ R f * HahnSeries.single b (1 : R)).coeff (a + b) =
      if 0 ≤ a then PowerSeries.coeff a.toNat f else 0 := by
  rw [HahnSeries.coeff_mul_single_add, mul_one]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [HahnSeries.ofPowerSeries_apply_coeff, Int.toNat_natCast]
  · exact coeff_ofPowerSeries_of_neg f (not_le.mp h)

end LaurentHelpers

section Dictionary

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "𝒪" => (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) : Type)

include hM hpM hζ hK hAp hζA hj in

private theorem exists_theta
    (u : 𝒪) (hu : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))))
    (P₀ : Ideal 𝒪) [P₀.IsPrime] (hP₀ : ∀ b : 𝒪, b ∈ P₀ ↔ (b : ↥K) ∈ W₀.nonunits) :
    ∃ θ : 𝒪 →+* LaurentSeries (ZMod p), RingHom.ker θ = P₀ ∧ MonicAt (θ u) (1 - p) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A 𝒪 a ∈ P₀) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨W, hWmem, hWA, hWm, hWgen, hWnu⟩ :=
    ModularCurve.XOneP.exists_gaussValuationSubring_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  have hWeq : W = W₀ := by ext f; rw [hWmem f, hW₀ f]
  have hA : ∀ a : A, algebraMap A ↥K a ∈ W₀ := fun a => hWeq ▸ hWA a
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits := fun a ha => hWeq ▸ hWm a ha
  have hgen : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀ := fun P hP => hWeq ▸ hWgen P hP
  have hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0) := fun f x y hy hf => hWeq ▸ hWnu f x y hy hf

  have hjW : j ∈ W₀ := by
    have h := (hgen Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rwa [Polynomial.aeval_X] at h
  have hadj : (Algebra.adjoin A ({j} : Set ↥K)).toSubring ≤ W₀.toSubring := by
    intro x hx
    change x ∈ Algebra.adjoin A ({j} : Set ↥K) at hx
    change x ∈ W₀
    induction hx using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hjW
    | algebraMap r => exact hA r
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | mul _ _ _ _ ha hb => exact mul_mem ha hb
  have hOW : ∀ b : 𝒪, (b : ↥K) ∈ W₀ := fun b =>
    mem_of_isIntegral_of_le W₀ hadj ((ModularCurve.TwoChart.mem_chartAlg_iff A (↥K)).mp b.2)

  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K A W₀ hW₀ hnu

  haveI hchar : CharP (IsLocalRing.ResidueField A) p :=
    IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
  let ι : ZMod p →+* IsLocalRing.ResidueField A := ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)
  have hιbij : Function.Bijective ι := by
    refine ⟨ι.injective, fun x => ?_⟩
    obtain ⟨n, hn⟩ :=
      IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp x
    exact ⟨(n : ZMod p), by rw [map_intCast, ← hn, eq_intCast]⟩
  let e : IsLocalRing.ResidueField A ≃+* ZMod p := (RingEquiv.ofBijective ι hιbij).symm
  have hinj : Function.Injective (ModularCurve.coeffMap (e : IsLocalRing.ResidueField A →+* ZMod p)) := by
    intro x y hxy
    have h := congrArg (ModularCurve.coeffMap (e.symm : ZMod p →+* IsLocalRing.ResidueField A)) hxy
    have hid : (e.symm : ZMod p →+* IsLocalRing.ResidueField A).comp (e : IsLocalRing.ResidueField A →+* ZMod p)
        = RingHom.id _ := RingHom.ext fun z => e.symm_apply_apply z
    rwa [ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_coeffMap, hid, ModularCurve.coeffMap_id,
      ModularCurve.coeffMap_id] at h

  let incl : 𝒪 →+* ↥W₀ :=
    { toFun := fun b => ⟨b, hOW b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨(ModularCurve.coeffMap (e : IsLocalRing.ResidueField A →+* ZMod p)).comp (red.comp incl), ?_, ?_, ?_⟩
  ·
    ext b
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, hP₀ b, map_eq_zero_iff _ hinj, ← RingHom.mem_ker, hker,
      ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨fun h => ⟨hOW b, h⟩, fun ⟨_, h⟩ => h⟩
  ·

    have hmemq : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (M * p) := by
      have hle : ModularCurve.modularFunctionFieldFull p ≤ ModularCurve.modularFunctionFieldFull (M * p) := by
        apply IntermediateField.adjoin.mono
        rintro x ⟨d, hd, hdq, rfl⟩
        exact ⟨d, hd, hdq.trans (dvd_mul_left p M), rfl⟩
      exact hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p)
    obtain ⟨Wq, hWq0, hWq1, -, -, -⟩ := ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd M p hpM
    obtain ⟨⟨x, -, hx⟩, -, -, -⟩ :=
      ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd M p hpM hmemq (Wq 0) (Wq 1) hWq0 hWq1
    have hxc : ∀ i : ℤ, ((x.coeff i : ℤ) : ℚ) = (ModularCurve.modularUnitSeries p).coeff i := fun i => by
      rw [hx, ModularCurve.coeffMap_coeff]; rfl
    have hx1 : x.coeff (1 - p) = 1 := by
      have h := hxc (1 - p); rw [ModularCurve.coeff_modularUnitSeries_self] at h; exact_mod_cast h
    have hx0 : ∀ i < 1 - (p : ℤ), x.coeff i = 0 := fun i hi => by
      have h := hxc i; rw [ModularCurve.coeff_modularUnitSeries_of_lt p hi] at h; exact_mod_cast h

    set xP : PowerSeries ℤ := PowerSeries.mk fun n => x.coeff ((n : ℤ) + (1 - p)) with hxP
    have hC1 : x * HahnSeries.single ((p : ℤ) - 1) (1 : ℤ) = HahnSeries.ofPowerSeries ℤ ℤ xP := by
      ext n
      have hn : n = (n - ((p : ℤ) - 1)) + ((p : ℤ) - 1) := by ring
      have hone : HahnSeries.ofPowerSeries ℤ ℤ xP = HahnSeries.ofPowerSeries ℤ ℤ xP * HahnSeries.single 0 (1 : ℤ) := by
        rw [← HahnSeries.C_apply, HahnSeries.C_one, mul_one]
      rw [hn, HahnSeries.coeff_mul_single_add, mul_one, hone, ← add_zero (n - ((p : ℤ) - 1) + ((p : ℤ) - 1)),
        coeff_ofPowerSeries_mul_single_add]
      split_ifs with h0
      · rw [hxP, PowerSeries.coeff_mk]; congr 1; omega
      · exact hx0 _ (by omega)
    have hpz : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by have := hp.one_le; omega
    set xA : PowerSeries A := xP.map (Int.castRingHom A) with hxA
    have hP1 : ((PowerSeries.X : PowerSeries A) ^ (p - 1)).map (IsLocalRing.residue A) ≠ 0 := by
      rw [map_pow, PowerSeries.map_X]; exact pow_ne_zero _ PowerSeries.X_ne_zero
    have hy : ((PowerSeries.X : PowerSeries A) ^ (p - 1)).map (algebraMap A L) = PowerSeries.X ^ (p - 1) := by
      rw [map_pow, PowerSeries.map_X]
    have hxL : xA.map (algebraMap A L) = xP.map (Int.castRingHom L) := by
      rw [hxA, ← RingHom.comp_apply (PowerSeries.map (algebraMap A L)), ← PowerSeries.map_comp,
        RingHom.ext_int ((algebraMap A L).comp (Int.castRingHom A)) (Int.castRingHom L)]
    have huL : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffMap (Int.castRingHom L) x := by
      rw [hu, hx]
      change ModularCurve.coeffMap (algebraMap ℚ L) (ModularCurve.coeffMap (Int.castRingHom ℚ) x) = _
      rw [ModularCurve.coeffMap_coeffMap]
      exact ModularCurve.coeffMap_congr (RingHom.ext_int _ _) x
    have hP2 : ((u : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L (((PowerSeries.X : PowerSeries A) ^ (p - 1)).map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L)) := by
      rw [hy, HahnSeries.ofPowerSeries_X_pow, hxL, ← coeffMap_ofPowerSeries, ← hC1, map_mul, ModularCurve.coeffMap_single,
        map_one (Int.castRingHom L), huL, hpz]
    have hred_u := hred (incl u) xA ((PowerSeries.X : PowerSeries A) ^ (p - 1)) hP1 hP2
    have hθu : ModularCurve.coeffMap (e : IsLocalRing.ResidueField A →+* ZMod p) (red (incl u)) =
        HahnSeries.ofPowerSeries ℤ (ZMod p) ((xA.map (IsLocalRing.residue A)).map (e : IsLocalRing.ResidueField A →+* ZMod p)) *
          HahnSeries.single (1 - (p : ℤ)) 1 := by
      rw [hred_u, map_pow, PowerSeries.map_X, HahnSeries.ofPowerSeries_X_pow, hpz, div_eq_mul_inv, HahnSeries.inv_single, inv_one,
        map_mul, coeffMap_ofPowerSeries, ModularCurve.coeffMap_single, map_one (e : IsLocalRing.ResidueField A →+* ZMod p),
        show -((p : ℤ) - 1) = 1 - (p : ℤ) by ring]
    rw [RingHom.comp_apply, RingHom.comp_apply, hθu]
    refine MonicAt.of_coeff ?_ (fun i hi => ?_)
    · have h := coeff_ofPowerSeries_mul_single_add
        ((xA.map (IsLocalRing.residue A)).map (e : IsLocalRing.ResidueField A →+* ZMod p)) 0 (1 - (p : ℤ))
      rw [zero_add] at h
      rw [h, if_pos le_rfl, Int.toNat_zero, PowerSeries.coeff_map, PowerSeries.coeff_map, hxA, PowerSeries.coeff_map, hxP,
        PowerSeries.coeff_mk, Nat.cast_zero, zero_add, hx1, map_one, map_one, map_one]
    · have h := coeff_ofPowerSeries_mul_single_add
        ((xA.map (IsLocalRing.residue A)).map (e : IsLocalRing.ResidueField A →+* ZMod p)) (i - (1 - (p : ℤ))) (1 - (p : ℤ))
      rw [sub_add_cancel] at h
      rw [h, if_neg (by omega)]
  ·
    intro a ha
    rw [hP₀, Subalgebra.coe_algebraMap]
    exact hm a ha

end Dictionary

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
  AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero (coord P u)
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

section Modular

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] {K : IntermediateField L (LaurentSeries L)}
  {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
  {j : ↥K}

set_option quotPrecheck false in
local notation "𝒪" => (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) : Type)
set_option quotPrecheck false in
local notation "k" => ZMod p

variable (P : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) [P.IsPrime]
  [Algebra (ZMod p) (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ P)]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsScalarTower A L ↥K] [P.IsPrime] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem algebraMap_base_mem_range [IsLocalRing A]
    (hsurj : Function.Surjective (algebraMap ℤ (IsLocalRing.ResidueField A)))
    (hmP : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A 𝒪 a ∈ P) (c : A) :
    algebraMap A (𝒪 ⧸ P) c ∈ Set.range (algebraMap k (𝒪 ⧸ P)) := by
  obtain ⟨n, hn⟩ := hsurj (IsLocalRing.residue A c)
  have hmem : c - (n : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_intCast, ← hn, eq_intCast, sub_self]
  refine ⟨(n : k), ?_⟩
  have h0 : algebraMap A (𝒪 ⧸ P) c = Ideal.Quotient.mk P (algebraMap A 𝒪 c) := rfl
  have h1 : Ideal.Quotient.mk P (algebraMap A 𝒪 (c - n)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hmP _ hmem)
  rw [map_sub, map_sub, map_intCast, map_intCast, sub_eq_zero] at h1
  rw [map_intCast, h0, h1]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsScalarTower A L ↥K] [P.IsPrime] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem finiteType_quotient [IsLocalRing A]
    (hsurj : Function.Surjective (algebraMap ℤ (IsLocalRing.ResidueField A)))
    (hmP : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A 𝒪 a ∈ P)
    (hFT : Algebra.FiniteType A 𝒪) : Algebra.FiniteType k (𝒪 ⧸ P) := by
  classical
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := A) (A := 𝒪)
  refine ⟨⟨S.image (Ideal.Quotient.mk P), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro b -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a ∈ Algebra.adjoin A (S : Set 𝒪) := by rw [hS]; exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  | algebraMap c =>
    obtain ⟨c', hc'⟩ := algebraMap_base_mem_range (p := p) P hsurj hmP c
    have h0 : Ideal.Quotient.mk P (algebraMap A 𝒪 c) = algebraMap A (𝒪 ⧸ P) c := rfl
    rw [h0, ← hc']
    exact Subalgebra.algebraMap_mem _ c'
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

omit [IsDomain A] [IsDiscreteValuationRing A] [IsScalarTower A L ↥K] [P.IsPrime] [Fact p.Prime]
  [Algebra (ZMod p) (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ P)] in

private theorem isIntegral_polynomial_chartAlgFin :
    letI := (Polynomial.aeval (R := A) (ModularCurve.TwoChart.jChartFin A (↥K) j)).toRingHom.toAlgebra
    Algebra.IsIntegral A[X] 𝒪 := by
  letI iXA : Algebra A[X] 𝒪 := (Polynomial.aeval (R := A) (ModularCurve.TwoChart.jChartFin A (↥K) j)).toRingHom.toAlgebra
  letI iXF : Algebra A[X] ↥K := (Polynomial.aeval (R := A) j).toRingHom.toAlgebra
  let f : A[X] →+* ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
    (Polynomial.aeval (R := A) j).toRingHom.codRestrict (Algebra.adjoin A ({j} : Set ↥K)).toSubring
      fun q => Polynomial.aeval_mem_adjoin_singleton A _
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨q, rfl⟩ := hy
    exact ⟨q, rfl⟩
  have hval : ∀ q : A[X], ((f q : ↥(Algebra.adjoin A ({j} : Set ↥K))) : ↥K) = algebraMap A[X] ↥K q := fun _ => rfl
  refine ⟨fun a => ?_⟩
  have h1 : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)) (a : ↥K) := (ModularCurve.TwoChart.mem_chartAlg_iff A (↥K)).mp a.2
  have h2 : IsIntegral A[X] (a : ↥K) := by
    obtain ⟨q, hqmon, hqev⟩ := h1
    have hlifts : q ∈ Polynomial.lifts f := (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => hf _
    obtain ⟨q', hq'q, -, hq'mon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmon
    refine ⟨q', hq'mon, ?_⟩
    have : algebraMap A[X] ↥K = (algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K)) ↥K).comp f :=
      RingHom.ext fun q => (hval q).symm
    rw [this, ← Polynomial.eval₂_map, hq'q]
    exact hqev
  let val : 𝒪 →ₐ[A[X]] ↥K :=
    { (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val.toRingHom with
      commutes' := fun q => by
        change (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val (Polynomial.aeval (ModularCurve.TwoChart.jChartFin A (↥K) j) q) =
          Polynomial.aeval j q
        rw [← Polynomial.aeval_algHom_apply]; rfl }
  exact (isIntegral_algHom_iff val Subtype.val_injective).mp h2

end Modular

end ModularCurve.XOneP.UnrSpecZero

namespace ModularCurve
p2m_export "ModularCurve" "TwoChart.mem_chartAlg_iff TwoChart.chartAlgFin TwoChart.jChartFin x1FunctionField jq modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange modularUnitSeries coeff_modularUnitSeries_self coeff_modularUnitSeries_of_lt XOneP.exists_gaussValuationSubring_x1_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd modularUnitSeries_mem_valuationSubring_pair_of_not_dvd modularUnitSeries_mem_modularFunctionFieldFull"
namespace XOneP
p2m_export "ModularCurve.XOneP" "exists_gaussValuationSubring_x1_mul"
namespace UnrSpecZero
namespace C6Nontrivial
p2m_open "ModularCurve.XOneP ModularCurve~coeffMap_ofPowerSeries"

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

end ModularCurve.XOneP.UnrSpecZero.C6Nontrivial

open ModularCurve.XOneP.UnrSpecZero in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
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
    (u : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hu : ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))))
    (P₀ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) [P₀.IsPrime] (hP₀ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ P₀ ↔ (b : ↥K) ∈ W₀.nonunits) :
    ∃ avoid : (ZMod p)[X], avoid ≠ 0 ∧
      ∀ h : ℤ[X], 0 < (h.map (Int.castRingHom (ZMod p))).natDegree → (h.map (Int.castRingHom (ZMod p))).Separable →
        IsCoprime (h.map (Int.castRingHom (ZMod p))) avoid →
        Nontrivial (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ (P₀ ⊔ Ideal.span {Polynomial.aeval u h})) ∧
        Algebra.FormallyUnramified ℤ (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ (P₀ ⊔ Ideal.span {Polynomial.aeval u h})) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨θ, hθ, hmono, hmP⟩ := exists_theta p M hM hpM L ζ hζ K hK A hAp hζA j hj u hu W₀ hW₀ P₀ hP₀
  have hpP : ((p : ℕ) : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ∈ P₀ := by
    have h := hmP (p : A) hAp
    rwa [map_natCast] at h
  letI : Algebra (ZMod p) (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ P₀) := algebraK P₀ hpP
  haveI : IsDomain (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ P₀) := Ideal.Quotient.isDomain P₀
  have hm0 : (1 - (p : ℤ)) < 0 := by have := hp.two_le; omega
  have hmq : -(1 - (p : ℤ)) < p := by omega

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p))
      hT L (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) rfl j hj
  haveI hsepK : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    haveI := hFD; exact Algebra.IsSeparable.of_integral _ _
  have hFT : Algebra.FiniteType A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsepK).1
  have hsurj := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp
  have hft := finiteType_quotient (p := p) P₀ hsurj hmP hFT
  have htr := transcendental_coord P₀ θ hθ u hmono hm0

  letI iXA : Algebra A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) :=
    (Polynomial.aeval (R := A) (ModularCurve.TwoChart.jChartFin A (↥K) j)).toRingHom.toAlgebra
  haveI : IsScalarTower A A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap _ _ c = Polynomial.aeval (ModularCurve.TwoChart.jChartFin A (↥K) j) (algebraMap _ _ c)
      rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI := isAlgebraic_adjoin_of_isIntegral P₀ isIntegral_polynomial_chartAlgFin (algebraMap_base_mem_range (p := p) P₀ hsurj hmP)
  have halg := isAlgebraic_adjoin_of_transcendental
    (coord P₀ (algebraMap A[X] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) Polynomial.X)) (coord P₀ u) htr

  obtain ⟨c, hc0, hc⟩ := exists_forall_formallyUnramified P₀ θ hθ u hmono hm0 hmq hft halg
  obtain ⟨f, hf0, hf⟩ := C6Nontrivial.exists_forall_not_isUnit_aeval_zmod hft (Ideal.Quotient.mk P₀ u) htr halg
  refine ⟨c * f, mul_ne_zero hc0 hf0, fun h hdeg hsep hcop => ?_⟩
  exact transport P₀ (Polynomial.aeval u h) _ (aeval_mk_map P₀ u h).symm (hf _ hdeg hcop.of_mul_right_right)
    (hc _ hsep hcop.of_mul_right_left)

end

end S_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul (solution)
