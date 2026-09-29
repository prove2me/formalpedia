-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0fe3e81f-4a7e-5783-8ed9-73f1db7f03be

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve"
open scoped IntermediateField MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.jAt XHDRLevel.coe_jAt XHDRLevel.chartAlgFin XHDRLevel.ΓM XHDRModelAtP translation_mem_GammaH Gamma1_le_GammaH qExpFunctionFieldC algebraMap_apply_eq_single modularFunctionFieldFull jqModC IgusaScheme.chartAlgFin IgusaScheme IsMonicOfOrder modularUnitSeries isMonicOfOrder_modularUnitSeries finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index transcendental_jq"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "comp"
namespace OggUnramHAux
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

section Generic

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]

theorem exists_ne_zero_forall_smul_kaehler_eq_zero
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

theorem isUnramifiedAt_of_forall_smul_eq_zero [Algebra.EssFiniteType R A] {a : A}
    (ha : ∀ ω : Ω[A⁄R], a • ω = 0) (P : Ideal A) [hP : P.IsPrime] (haP : a ∉ P) :
    Algebra.IsUnramifiedAt R P := by
  have hmem : a ∈ Module.annihilator A Ω[A⁄R] := Module.mem_annihilator.mpr ha
  change (⟨P, hP⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R A
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, Module.support_eq_zeroLocus]
  exact fun h => haP (h hmem)

theorem exists_ne_zero_algebraMap_mem_span {a : A} (ha0 : a ≠ 0) (ha : IsAlgebraic R a) :
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

end Generic

section Laurent

theorem isMonicOfOrder_pow {f : LaurentSeries ℚ} {m : ℤ} (hf : IsMonicOfOrder f m) (i : ℕ) :
    IsMonicOfOrder (f ^ i) (i * m) := by
  induction i with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact ⟨HahnSeries.order_one, HahnSeries.leadingCoeff_one⟩
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact ih.mul hf

theorem transcendental_of_isMonicOfOrder {f : LaurentSeries ℚ} {m : ℤ} (hf : IsMonicOfOrder f m) (hm : m < 0) :
    Transcendental ℚ f := by
  rintro ⟨P, hP0, hP⟩
  apply Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hcoeff : (Polynomial.aeval f P).coeff ((P.natDegree : ℤ) * m) = P.leadingCoeff := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single P.natDegree]
    · rw [Algebra.smul_def, algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
        (isMonicOfOrder_pow hf P.natDegree).coeff_self, mul_one, Polynomial.leadingCoeff]
    · intro i hi hne
      have hid : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      have hlt : (P.natDegree : ℤ) * m < (i : ℤ) * m :=
        mul_lt_mul_of_neg_right (by exact_mod_cast hid) hm
      rw [Algebra.smul_def, algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
        (isMonicOfOrder_pow hf i).coeff_of_lt hlt, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  rw [← hcoeff, hP, HahnSeries.coeff_zero]

end Laurent

open AlgebraicCurve.TwoChartIntegralModel

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [Fact q.Prime]
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev Rq : Type := ↥(GaloisRep.ratLocalizedAt q)

abbrev FF : Type := ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H))

abbrev AF : Type := ↥(XHDRLevel.chartAlgFin q (XHDRLevel.ΓM M H) hj)

abbrev jF : FF M H := XHDRLevel.jAt (XHDRLevel.ΓM M H) hj

abbrev Kj : IntermediateField ℚ (FF M H) := IntermediateField.adjoin ℚ ({jF M H hj} : Set (FF M H))

scoped instance fact_FiniteIndex : (XHDRLevel.ΓM M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem finiteDimensional_Kj : FiniteDimensional ↥(Kj M H hj) (FF M H) := by

  have h := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (XHDRLevel.ΓM M H)
    (ModularCurve.translation_mem_GammaH M H) (XHDRLevel.ΓM M H) le_rfl (fun γ hγ => Or.inl hγ)
    (XHDRLevel.jAt (XHDRLevel.ΓM M H) hj) (XHDRLevel.coe_jAt _ hj)).1

  have hmap : @algebraMap ℚ (FF M H) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H))) = algebraMap ℚ (FF M H) :=
    RingHom.ext fun r => (eq_ratCast _ r).trans (eq_ratCast _ r).symm
  have hsub : (@IntermediateField.toSubfield ℚ (FF M H) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H)))
        (@IntermediateField.adjoin ℚ _ (FF M H) _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H))) ({XHDRLevel.jAt (XHDRLevel.ΓM M H) hj} : Set (FF M H)))) =
      (Kj M H hj).toSubfield := by
    show _ = (IntermediateField.adjoin ℚ ({XHDRLevel.jAt (XHDRLevel.ΓM M H) hj} : Set (FF M H))).toSubfield
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, hmap]

  have h' : FiniteDimensional ↥(@IntermediateField.toSubfield ℚ (FF M H) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H)))
        (@IntermediateField.adjoin ℚ _ (FF M H) _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H))) ({XHDRLevel.jAt (XHDRLevel.ΓM M H) hj} : Set (FF M H)))) (FF M H) := h
  rw [hsub] at h'
  exact h'

scoped instance instIsScalarTowerRatLaurent : IsScalarTower ℚ ℚ (LaurentSeries ℚ) := ⟨fun a b c => mul_smul a b c⟩

omit [NeZero M] in

theorem transcendental_of_coe {x : FF M H} (hx : Transcendental ℚ (x : LaurentSeries ℚ)) : Transcendental ℚ x := by
  intro halg
  apply hx
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  let ι : FF M H →+* LaurentSeries ℚ := SubringClass.subtype (qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H))
  have h := congrArg ι hP
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
  have hring : ι.comp (algebraMap ℚ (FF M H)) = algebraMap ℚ (LaurentSeries ℚ) := RingHom.ext_rat _ _
  rw [hring] at h
  rw [Polynomial.aeval_def]
  exact h

omit [NeZero M] in

theorem transcendental_v (v : FF M H)
    (hv : (v : LaurentSeries ℚ) = modularUnitSeries q ∨
      (v : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    Transcendental ℚ v := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hu : Transcendental ℚ (modularUnitSeries q) :=
    transcendental_of_isMonicOfOrder (isMonicOfOrder_modularUnitSeries q) (by omega)
  rcases hv with h | h
  · exact transcendental_of_coe M H (by rw [h]; exact hu)
  · haveI : CharZero (LaurentSeries ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries ℚ)).injective
    have hqL : ((q : LaurentSeries ℚ) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
    have e1 : (((q : FF M H) ^ 12 * v⁻¹ : FF M H) : LaurentSeries ℚ) =
        (q : LaurentSeries ℚ) ^ 12 * (v : LaurentSeries ℚ)⁻¹ := by
      push_cast; rfl
    have hw : (((q : FF M H) ^ 12 * v⁻¹ : FF M H) : LaurentSeries ℚ) = modularUnitSeries q := by
      rw [e1, h, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hqL, one_mul]
    have hwt : Transcendental ℚ ((q : FF M H) ^ 12 * v⁻¹ : FF M H) :=
      transcendental_of_coe M H (by rw [hw]; exact hu)
    intro halg
    apply hwt
    have hmem : ((q : FF M H) ^ 12 * v⁻¹ : FF M H) ∈ algebraicClosure ℚ (FF M H) :=
      mul_mem (pow_mem (natCast_mem _ q) 12) (inv_mem (mem_algebraicClosure_iff.mpr halg))
    exact mem_algebraicClosure_iff.mp hmem

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in
omit [NeZero M] in
theorem isFractionRing_polynomial_adjoin (x : FF M H) (hx : Transcendental ℚ x) :
    letI : Algebra ℚ[X] ↥ℚ⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x)).toRingHom.toAlgebra
    IsFractionRing ℚ[X] ↥ℚ⟮x⟯ := by
  letI : Algebra ℚ[X] ↥ℚ⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x)).toRingHom.toAlgebra
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental ℚ (FF M H) x hx
  have halg : ∀ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f = aeval RatFunc.X f := fun f => by
    have h1 := aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X f
    rw [aeval_X_left, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_X] at h1
    exact h1.symm
  have hcomm : ∀ f : ℚ[X], e.symm.toRingEquiv (algebraMap ℚ[X] (RatFunc ℚ) f) = algebraMap ℚ[X] ↥ℚ⟮x⟯ f := by
    intro f
    change e.symm.toRingEquiv (algebraMap ℚ[X] (RatFunc ℚ) f) = aeval (IntermediateField.AdjoinSimple.gen ℚ x) f
    rw [halg, AlgEquiv.coe_ringEquiv, ← aeval_algHom_apply, ← he, AlgEquiv.symm_apply_apply]
    rfl
  let e' : RatFunc ℚ ≃ₐ[ℚ[X]] ↥ℚ⟮x⟯ := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) hcomm
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors ℚ[X]) e'

open scoped IntermediateField.algebraAdjoinAdjoin in
include hj in
theorem isAlgebraic_adjoin_simple (x : FF M H) (hx : Transcendental ℚ x) : Algebra.IsAlgebraic ↥ℚ⟮x⟯ (FF M H) := by
  haveI := finiteDimensional_Kj M H hj
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({jF M H hj} : Set (FF M H))) (FF M H) :=
    Algebra.IsAlgebraic.trans (R := ↥(Algebra.adjoin ℚ ({jF M H hj} : Set (FF M H)))) (S := ↥(Kj M H hj)) (A := FF M H)
  have htr : Algebra.trdeg ℚ (FF M H) ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({jF M H hj} : Set (FF M H))
    rwa [Cardinal.mk_singleton] at h
  have h1 : AlgebraicIndependent ℚ ![x] := algebraicIndependent_iff_transcendental.mpr hx
  have hb : IsTranscendenceBasis ℚ ![x] := h1.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have h := hb.isAlgebraic_field
  have hr : Set.range ![x] = {x} := by simp
  rwa [hr] at h

theorem isFractionRing_chartAlgFin : IsFractionRing (AF M H q hj) (FF M H) := by
  haveI : IsFractionRing (Rq q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  haveI := finiteDimensional_Kj M H hj
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({jF M H hj} : Set (FF M H))) (FF M H) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (Rq q) ℚ (FF M H) ({jF M H hj} : Set (FF M H))

attribute [local instance] Polynomial.algebra in
set_option maxHeartbeats 6400000 in
theorem main (v : AF M H q hj)
    (hv : ((v : FF M H) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : FF M H) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    letI : Algebra (Rq q)[X] (AF M H q hj) := (Polynomial.aeval (R := Rq q) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal (AF M H q hj)) [P.IsPrime],
      P.comap (algebraMap (Rq q) (AF M H q hj)) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt (Rq q)[X] P := by
  have hvt : Transcendental ℚ (v : FF M H) := transcendental_v M H q v hv
  set vF : FF M H := (v : FF M H) with hvF
  haveI : IsFractionRing (Rq q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q

  letI iA : Algebra (Rq q)[X] (AF M H q hj) := (Polynomial.aeval (R := Rq q) v).toRingHom.toAlgebra
  letI iF : Algebra (Rq q)[X] (FF M H) := ((algebraMap (AF M H q hj) (FF M H)).comp (algebraMap (Rq q)[X] (AF M H q hj))).toAlgebra
  haveI tAF : IsScalarTower (Rq q)[X] (AF M H q hj) (FF M H) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF : ∀ f : (Rq q)[X], algebraMap (Rq q)[X] (FF M H) f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (XHDRLevel.chartAlgFin q (XHDRLevel.ΓM M H) hj).val v f).symm
  letI iQXF : Algebra ℚ[X] (FF M H) := (Polynomial.aeval vF).toRingHom.toAlgebra
  letI iQXK : Algebra ℚ[X] ↥ℚ⟮vF⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ vF)).toRingHom.toAlgebra
  letI iRXK : Algebra (Rq q)[X] ↥ℚ⟮vF⟯ := ((algebraMap ℚ[X] ↥ℚ⟮vF⟯).comp (algebraMap (Rq q)[X] ℚ[X])).toAlgebra
  haveI tRQK : IsScalarTower (Rq q)[X] ℚ[X] ↥ℚ⟮vF⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI tQKF : IsScalarTower ℚ[X] ↥ℚ⟮vF⟯ (FF M H) := IsScalarTower.of_algebraMap_eq fun f => by
    change Polynomial.aeval vF f = ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ vF) f : ↥ℚ⟮vF⟯) : FF M H)
    exact Polynomial.aeval_algHom_apply (ℚ⟮vF⟯).val (IntermediateField.AdjoinSimple.gen ℚ vF) f
  haveI tRQF : IsScalarTower (Rq q)[X] ℚ[X] (FF M H) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF]
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap (Rq q) ℚ) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI tRKF : IsScalarTower (Rq q)[X] ↥ℚ⟮vF⟯ (FF M H) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [IsScalarTower.algebraMap_apply (Rq q)[X] ℚ[X] (FF M H), IsScalarTower.algebraMap_apply ℚ[X] ↥ℚ⟮vF⟯ (FF M H)]
    rfl

  haveI : IsLocalization ((nonZeroDivisors (Rq q)).map (C : Rq q →+* (Rq q)[X])) ℚ[X] := Polynomial.isLocalization _ ℚ
  haveI : IsFractionRing ℚ[X] ↥ℚ⟮vF⟯ := isFractionRing_polynomial_adjoin M H vF hvt
  haveI : Algebra.FormallyUnramified (Rq q)[X] ℚ[X] :=
    Algebra.FormallyUnramified.of_isLocalization ((nonZeroDivisors (Rq q)).map (C : Rq q →+* (Rq q)[X]))
  haveI : Algebra.FormallyUnramified ℚ[X] ↥ℚ⟮vF⟯ :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℚ[X])
  haveI : Algebra.FormallyUnramified (Rq q)[X] ↥ℚ⟮vF⟯ := Algebra.FormallyUnramified.comp (Rq q)[X] ℚ[X] ↥ℚ⟮vF⟯
  haveI : Algebra.IsAlgebraic ↥ℚ⟮vF⟯ (FF M H) := isAlgebraic_adjoin_simple M H hj vF hvt
  haveI : Algebra.FormallyUnramified ↥ℚ⟮vF⟯ (FF M H) := Algebra.FormallyUnramified.of_isSeparable ↥ℚ⟮vF⟯ (FF M H)
  haveI : Algebra.FormallyUnramified (Rq q)[X] (FF M H) := Algebra.FormallyUnramified.comp (Rq q)[X] ↥ℚ⟮vF⟯ (FF M H)

  haveI : Algebra.FiniteType (Rq q) (AF M H q hj) :=
    (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC q (XHDRLevel.ΓM M H)
      (ModularCurve.translation_mem_GammaH M H) (XHDRLevel.jAt (XHDRLevel.ΓM M H) hj) (XHDRLevel.coe_jAt _ hj)).1
  haveI : IsScalarTower (Rq q) (Rq q)[X] (AF M H q hj) := IsScalarTower.of_algebraMap_eq fun n => by
    change algebraMap (Rq q) (AF M H q hj) n = Polynomial.aeval v (algebraMap (Rq q) (Rq q)[X] n)
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI : Algebra.FiniteType (Rq q)[X] (AF M H q hj) := Algebra.FiniteType.of_restrictScalars_finiteType (Rq q) (Rq q)[X] (AF M H q hj)
  haveI : IsFractionRing (AF M H q hj) (FF M H) := isFractionRing_chartAlgFin M H q hj

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_smul_kaehler_eq_zero (R := (Rq q)[X]) (A := AF M H q hj) (FF M H)

  letI jA : Algebra ℤ[X] (AF M H q hj) := (Polynomial.aeval (R := ℤ) v).toRingHom.toAlgebra
  letI jF : Algebra ℤ[X] (FF M H) := ((algebraMap (AF M H q hj) (FF M H)).comp (algebraMap ℤ[X] (AF M H q hj))).toAlgebra
  haveI uAF : IsScalarTower ℤ[X] (AF M H q hj) (FF M H) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF' : ∀ f : ℤ[X], algebraMap ℤ[X] (FF M H) f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (XHDRLevel.chartAlgFin q (XHDRLevel.ΓM M H) hj).val.toRingHom.toIntAlgHom v f).symm
  haveI uZQF : IsScalarTower ℤ[X] ℚ[X] (FF M H) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF']
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap ℤ ℚ) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) ℚ[X] := Polynomial.isLocalization _ ℚ
  have haalg : IsAlgebraic ℤ[X] a := by
    have h1 : IsAlgebraic ↥ℚ⟮vF⟯ (a : FF M H) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℚ[X] (a : FF M H) := (IsFractionRing.isAlgebraic_iff ℚ[X] ↥ℚ⟮vF⟯ (FF M H)).mpr h1
    haveI : Algebra.IsAlgebraic ℤ[X] ℚ[X] :=
      IsLocalization.isAlgebraic ℚ[X] ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X]))
    have h3 : IsAlgebraic ℤ[X] (a : FF M H) := h2.restrictScalars ℤ[X]
    exact (isAlgebraic_algebraMap_iff (R := ℤ[X]) (S := AF M H q hj) (A := FF M H) Subtype.val_injective).mp h3
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_algebraMap_mem_span ha0 haalg
  refine ⟨c, hc0, fun P _ _ hcP => ?_⟩
  exact isUnramifiedAt_of_forall_smul_eq_zero ha P fun haP => hcP ((Ideal.span_singleton_le_iff_mem P).mpr haP hc)

end ModularCurve.XHDRModelAtP.OggUnramHAux
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve.XHDRModelAtP P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve.XHDRModelAtP.OggUnramHAux"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve.XHDRModelAtP"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve.XHDRModelAtP P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve.XHDRModelAtP.OggUnramHAux"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin.ModularCurve ModularCurve.XHDRLevel Polynomial AlgebraicGeometry.Polynomial"
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹) :
    letI : Algebra (R p)[X] ↥(chartAlgFin p (ΓM M H) hj) := (Polynomial.aeval (R := R p) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [P.IsPrime],
      P.comap (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt (R p)[X] P :=
  ModularCurve.XHDRModelAtP.OggUnramHAux.main M H p hj v hv

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem_chartAlgFin (solution)
