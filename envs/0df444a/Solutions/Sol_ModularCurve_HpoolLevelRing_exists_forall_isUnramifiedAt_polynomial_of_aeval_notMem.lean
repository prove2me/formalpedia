-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8ef33430-84b4-5525-aa10-03a88e6bec36

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_int_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.HpoolLevelRing"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsMonicOfOrder modularUnitSeries isMonicOfOrder_modularUnitSeries algebraMap_apply_eq_single modularFunctionFieldFull IgusaScheme.jFull IgusaScheme IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf finiteDimensional_adjoin_jFull_modularFunctionFieldFull"
namespace HpoolLevelRing
p2m_export "ModularCurve.HpoolLevelRing" "Afin"
namespace OggUnramAux
p2m_open "ModularCurve.HpoolLevelRing ModularCurve"

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

variable (p : ℕ) [Fact p.Prime] [NeZero p]

abbrev FF : Type := ↥(modularFunctionFieldFull p)

abbrev jF : FF p := IgusaScheme.jFull p

abbrev Kj : IntermediateField ℚ (FF p) := IntermediateField.adjoin ℚ ({jF p} : Set (FF p))

scoped instance finiteDimensional_Kj : FiniteDimensional ↥(Kj p) (FF p) :=
  ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p

scoped instance instIsScalarTowerRatLaurent : IsScalarTower ℚ ℚ (LaurentSeries ℚ) := ⟨fun a b c => mul_smul a b c⟩

omit [Fact p.Prime] [NeZero p] in

theorem transcendental_of_coe {x : FF p} (hx : Transcendental ℚ (x : LaurentSeries ℚ)) : Transcendental ℚ x := by
  intro halg
  apply hx
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  let ι : FF p →+* LaurentSeries ℚ := SubringClass.subtype (modularFunctionFieldFull p)
  have h := congrArg ι hP
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
  have hring : ι.comp (algebraMap ℚ (FF p)) = algebraMap ℚ (LaurentSeries ℚ) := RingHom.ext_rat _ _
  rw [hring] at h
  rw [Polynomial.aeval_def]
  exact h

omit [Fact p.Prime] in
theorem transcendental_uF (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) (hp : 2 ≤ p) :
    Transcendental ℚ (⟨modularUnitSeries p, hmem⟩ : FF p) :=
  transcendental_of_coe p (transcendental_of_isMonicOfOrder (isMonicOfOrder_modularUnitSeries p) (by omega))

theorem transcendental_v (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) (v : FF p)
    (hv : v = ⟨modularUnitSeries p, hmem⟩ ∨ v = (p : FF p) ^ 12 * (⟨modularUnitSeries p, hmem⟩)⁻¹) :
    Transcendental ℚ v := by
  have hu := transcendental_uF p hmem (Fact.out : p.Prime).two_le
  rcases hv with rfl | rfl
  · exact hu
  · intro halg
    apply hu
    set u : FF p := ⟨modularUnitSeries p, hmem⟩ with hu_def
    have hp0 : ((p : FF p) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
    have hmemv : (p : FF p) ^ 12 * u⁻¹ ∈ algebraicClosure ℚ (FF p) := mem_algebraicClosure_iff.mpr halg
    have hmemp : (p : FF p) ^ 12 ∈ algebraicClosure ℚ (FF p) := pow_mem (natCast_mem _ p) 12
    have hmemu : u ∈ algebraicClosure ℚ (FF p) := by
      have h := mul_mem (inv_mem hmemv) hmemp
      rwa [mul_inv, inv_inv, mul_assoc, mul_comm u, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul] at h
    exact mem_algebraicClosure_iff.mp hmemu

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in
omit [Fact p.Prime] [NeZero p] in
theorem isFractionRing_polynomial_adjoin (x : FF p) (hx : Transcendental ℚ x) :
    letI : Algebra ℚ[X] ↥ℚ⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x)).toRingHom.toAlgebra
    IsFractionRing ℚ[X] ↥ℚ⟮x⟯ := by
  letI : Algebra ℚ[X] ↥ℚ⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x)).toRingHom.toAlgebra
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental ℚ (FF p) x hx
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
theorem isAlgebraic_adjoin_simple (x : FF p) (hx : Transcendental ℚ x) : Algebra.IsAlgebraic ↥ℚ⟮x⟯ (FF p) := by
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({jF p} : Set (FF p))) (FF p) :=
    Algebra.IsAlgebraic.trans (R := ↥(Algebra.adjoin ℚ ({jF p} : Set (FF p)))) (S := ↥(Kj p)) (A := FF p)
  have htr : Algebra.trdeg ℚ (FF p) ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({jF p} : Set (FF p))
    rwa [Cardinal.mk_singleton] at h
  have h1 : AlgebraicIndependent ℚ ![x] := algebraicIndependent_iff_transcendental.mpr hx
  have hb : IsTranscendenceBasis ℚ ![x] := h1.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have h := hb.isAlgebraic_field
  have hr : Set.range ![x] = {x} := by simp
  rwa [hr] at h

attribute [local instance] Polynomial.algebra in
set_option maxHeartbeats 6400000 in
theorem main (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) (v : Afin p)
    (hv : (v : FF p) = ⟨modularUnitSeries p, hmem⟩ ∨ (v : FF p) = (p : FF p) ^ 12 * (⟨modularUnitSeries p, hmem⟩)⁻¹) :
    letI : Algebra ℤ[X] (Afin p) := (Polynomial.aeval v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal (Afin p)) [P.IsPrime],
      P.comap (algebraMap ℤ (Afin p)) = ⊥ → Polynomial.aeval v c₀' ∉ P → Algebra.IsUnramifiedAt ℤ[X] P := by
  have hvt : Transcendental ℚ (v : FF p) := transcendental_v p hmem v hv
  set vF : FF p := (v : FF p) with hvF

  letI iA : Algebra ℤ[X] (Afin p) := (Polynomial.aeval v).toRingHom.toAlgebra
  letI iF : Algebra ℤ[X] (FF p) := ((algebraMap (Afin p) (FF p)).comp (algebraMap ℤ[X] (Afin p))).toAlgebra
  haveI tAF : IsScalarTower ℤ[X] (Afin p) (FF p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF : ∀ f : ℤ[X], algebraMap ℤ[X] (FF p) f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (chartAlgFin ℤ (FF p) (jF p)).val v f).symm
  letI iQXF : Algebra ℚ[X] (FF p) := (Polynomial.aeval vF).toRingHom.toAlgebra
  letI iQXK : Algebra ℚ[X] ↥ℚ⟮vF⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ vF)).toRingHom.toAlgebra
  letI iZXK : Algebra ℤ[X] ↥ℚ⟮vF⟯ := ((algebraMap ℚ[X] ↥ℚ⟮vF⟯).comp (algebraMap ℤ[X] ℚ[X])).toAlgebra
  haveI tZQK : IsScalarTower ℤ[X] ℚ[X] ↥ℚ⟮vF⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI tQKF : IsScalarTower ℚ[X] ↥ℚ⟮vF⟯ (FF p) := IsScalarTower.of_algebraMap_eq fun f => by
    change Polynomial.aeval vF f = ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ vF) f : ↥ℚ⟮vF⟯) : FF p)
    exact Polynomial.aeval_algHom_apply (ℚ⟮vF⟯).val (IntermediateField.AdjoinSimple.gen ℚ vF) f
  haveI tZQF : IsScalarTower ℤ[X] ℚ[X] (FF p) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF]
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap ℤ ℚ) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI tZKF : IsScalarTower ℤ[X] ↥ℚ⟮vF⟯ (FF p) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [IsScalarTower.algebraMap_apply ℤ[X] ℚ[X] (FF p), IsScalarTower.algebraMap_apply ℚ[X] ↥ℚ⟮vF⟯ (FF p)]
    rfl

  haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) ℚ[X] := Polynomial.isLocalization _ ℚ
  haveI : IsFractionRing ℚ[X] ↥ℚ⟮vF⟯ := isFractionRing_polynomial_adjoin p vF hvt
  haveI : Algebra.FormallyUnramified ℤ[X] ℚ[X] :=
    Algebra.FormallyUnramified.of_isLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X]))
  haveI : Algebra.FormallyUnramified ℚ[X] ↥ℚ⟮vF⟯ :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℚ[X])
  haveI : Algebra.FormallyUnramified ℤ[X] ↥ℚ⟮vF⟯ := Algebra.FormallyUnramified.comp ℤ[X] ℚ[X] ↥ℚ⟮vF⟯
  haveI : Algebra.IsAlgebraic ↥ℚ⟮vF⟯ (FF p) := isAlgebraic_adjoin_simple p vF hvt
  haveI : Algebra.FormallyUnramified ↥ℚ⟮vF⟯ (FF p) := Algebra.FormallyUnramified.of_isSeparable ↥ℚ⟮vF⟯ (FF p)
  haveI : Algebra.FormallyUnramified ℤ[X] (FF p) := Algebra.FormallyUnramified.comp ℤ[X] ↥ℚ⟮vF⟯ (FF p)

  haveI : Algebra.FiniteType ℤ (Afin p) := (ModularCurve.IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf p).1
  haveI : IsScalarTower ℤ ℤ[X] (Afin p) := IsScalarTower.of_algebraMap_eq fun n => by
    change algebraMap ℤ (Afin p) n = Polynomial.aeval v (algebraMap ℤ ℤ[X] n)
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI : Algebra.FiniteType ℤ[X] (Afin p) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ ℤ[X] (Afin p)
  haveI : IsFractionRing (Afin p) (FF p) :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg ℤ ℚ (FF p) ({jF p} : Set (FF p))

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_smul_kaehler_eq_zero (R := ℤ[X]) (A := Afin p) (FF p)
  have haalg : IsAlgebraic ℤ[X] a := by
    have h1 : IsAlgebraic ↥ℚ⟮vF⟯ (a : FF p) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℚ[X] (a : FF p) := (IsFractionRing.isAlgebraic_iff ℚ[X] ↥ℚ⟮vF⟯ (FF p)).mpr h1
    haveI : Algebra.IsAlgebraic ℤ[X] ℚ[X] :=
      IsLocalization.isAlgebraic ℚ[X] ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X]))
    have h3 : IsAlgebraic ℤ[X] (a : FF p) := h2.restrictScalars ℤ[X]
    exact (isAlgebraic_algebraMap_iff (R := ℤ[X]) (S := Afin p) (A := FF p) Subtype.val_injective).mp h3
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_algebraMap_mem_span ha0 haalg
  refine ⟨c, hc0, fun P _ _ hcP => ?_⟩
  exact isUnramifiedAt_of_forall_smul_eq_zero ha P fun haP => hcP ((Ideal.span_singleton_le_iff_mem P).mpr haP hc)

end ModularCurve.HpoolLevelRing.OggUnramAux
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.HpoolLevelRing.OggUnramAux"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.HpoolLevelRing"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.HpoolLevelRing.OggUnramAux"

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : Afin p)
    (hv : (v : ↥(modularFunctionFieldFull p)) = (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p)) ∨
      (v : ↥(modularFunctionFieldFull p)) = (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹) :
    letI : Algebra ℤ[X] (Afin p) := (Polynomial.aeval v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal (Afin p)) [P.IsPrime],
      P.comap (algebraMap ℤ (Afin p)) = ⊥ → Polynomial.aeval v c₀' ∉ P → Algebra.IsUnramifiedAt ℤ[X] P :=
  ModularCurve.HpoolLevelRing.OggUnramAux.main p hmem v hv

end S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem (solution)
