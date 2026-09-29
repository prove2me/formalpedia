-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2e8dcf39-fd96-531b-8425-e7a2b107c13d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve ModularCurve.IgusaScheme"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel IgusaScheme.jFull IgusaScheme.chartAlg IgusaScheme.chartAlgFin IgusaScheme algebraMap_apply_eq_single modularFunctionFieldFull IsMonicOfOrder modularUnitSeries isMonicOfOrder_modularUnitSeries IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf IgusaScheme.chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast finiteDimensional_adjoin_jFull_modularFunctionFieldFull"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "comp"
namespace OggUnramLevelAux
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

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

variable (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]

abbrev Rq : Type := ↥(GaloisRep.ratLocalizedAt q)

abbrev FF : Type := ↥(modularFunctionFieldFull N)

abbrev AF : Type := ↥(IgusaScheme.chartAlgFin N q)

abbrev jF : FF N := IgusaScheme.jFull N

abbrev Kj : IntermediateField ℚ (FF N) := IntermediateField.adjoin ℚ ({jF N} : Set (FF N))

scoped instance finiteDimensional_Kj : FiniteDimensional ↥(Kj N) (FF N) :=
  ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull N

scoped instance instIsScalarTowerRatLaurent : IsScalarTower ℚ ℚ (LaurentSeries ℚ) := ⟨fun a b c => mul_smul a b c⟩

omit [NeZero N] in

theorem transcendental_of_coe {x : FF N} (hx : Transcendental ℚ (x : LaurentSeries ℚ)) : Transcendental ℚ x := by
  intro halg
  apply hx
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  let ι : FF N →+* LaurentSeries ℚ := SubringClass.subtype (modularFunctionFieldFull N)
  have h := congrArg ι hP
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
  have hring : ι.comp (algebraMap ℚ (FF N)) = algebraMap ℚ (LaurentSeries ℚ) := RingHom.ext_rat _ _
  rw [hring] at h
  rw [Polynomial.aeval_def]
  exact h

omit [NeZero N] in

theorem transcendental_v (v : FF N)
    (hv : (v : LaurentSeries ℚ) = modularUnitSeries q ∨
      (v : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    Transcendental ℚ v := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hu : Transcendental ℚ (modularUnitSeries q) :=
    transcendental_of_isMonicOfOrder (isMonicOfOrder_modularUnitSeries q) (by omega)
  rcases hv with h | h
  · exact transcendental_of_coe N (by rw [h]; exact hu)
  · haveI : CharZero (LaurentSeries ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries ℚ)).injective
    have hqL : ((q : LaurentSeries ℚ) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
    have e1 : (((q : FF N) ^ 12 * v⁻¹ : FF N) : LaurentSeries ℚ) =
        (q : LaurentSeries ℚ) ^ 12 * (v : LaurentSeries ℚ)⁻¹ := by
      push_cast; rfl
    have hw : (((q : FF N) ^ 12 * v⁻¹ : FF N) : LaurentSeries ℚ) = modularUnitSeries q := by
      rw [e1, h, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hqL, one_mul]
    have hwt : Transcendental ℚ ((q : FF N) ^ 12 * v⁻¹ : FF N) :=
      transcendental_of_coe N (by rw [hw]; exact hu)
    intro halg
    apply hwt
    have hmem : ((q : FF N) ^ 12 * v⁻¹ : FF N) ∈ algebraicClosure ℚ (FF N) :=
      mul_mem (pow_mem (natCast_mem _ q) 12) (inv_mem (mem_algebraicClosure_iff.mpr halg))
    exact mem_algebraicClosure_iff.mp hmem

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in
omit [NeZero N] in
theorem isFractionRing_polynomial_adjoin (x : FF N) (hx : Transcendental ℚ x) :
    letI : Algebra ℚ[X] ↥ℚ⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x)).toRingHom.toAlgebra
    IsFractionRing ℚ[X] ↥ℚ⟮x⟯ := by
  letI : Algebra ℚ[X] ↥ℚ⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x)).toRingHom.toAlgebra
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental ℚ (FF N) x hx
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
theorem isAlgebraic_adjoin_simple (x : FF N) (hx : Transcendental ℚ x) : Algebra.IsAlgebraic ↥ℚ⟮x⟯ (FF N) := by
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({jF N} : Set (FF N))) (FF N) :=
    Algebra.IsAlgebraic.trans (R := ↥(Algebra.adjoin ℚ ({jF N} : Set (FF N)))) (S := ↥(Kj N)) (A := FF N)
  have htr : Algebra.trdeg ℚ (FF N) ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({jF N} : Set (FF N))
    rwa [Cardinal.mk_singleton] at h
  have h1 : AlgebraicIndependent ℚ ![x] := algebraicIndependent_iff_transcendental.mpr hx
  have hb : IsTranscendenceBasis ℚ ![x] := h1.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have h := hb.isAlgebraic_field
  have hr : Set.range ![x] = {x} := by simp
  rwa [hr] at h

theorem isFractionRing_chartAlgFin : IsFractionRing (AF N q) (FF N) := by
  haveI : IsFractionRing (Rq q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({jF N} : Set (FF N))) (FF N) :=
    Algebra.IsAlgebraic.of_finite _ _
  have h1 := (ModularCurve.IgusaScheme.chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast
    N q ({jF N} : Set (FF N))).1
  show IsFractionRing ↥(IgusaScheme.chartAlg N q ({jF N} : Set (FF N))) (FF N)
  rw [h1]
  exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (Rq q) ℚ (FF N) ({jF N} : Set (FF N))

attribute [local instance] Polynomial.algebra in
set_option maxHeartbeats 6400000 in
theorem main (v : AF N q)
    (hv : ((v : FF N) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : FF N) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    letI : Algebra (Rq q)[X] (AF N q) := (Polynomial.aeval (R := Rq q) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal (AF N q)) [P.IsPrime],
      P.comap (algebraMap (Rq q) (AF N q)) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt (Rq q)[X] P := by
  have hvt : Transcendental ℚ (v : FF N) := transcendental_v N q v hv
  set vF : FF N := (v : FF N) with hvF
  haveI : IsFractionRing (Rq q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q

  letI iA : Algebra (Rq q)[X] (AF N q) := (Polynomial.aeval (R := Rq q) v).toRingHom.toAlgebra
  letI iF : Algebra (Rq q)[X] (FF N) := ((algebraMap (AF N q) (FF N)).comp (algebraMap (Rq q)[X] (AF N q))).toAlgebra
  haveI tAF : IsScalarTower (Rq q)[X] (AF N q) (FF N) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF : ∀ f : (Rq q)[X], algebraMap (Rq q)[X] (FF N) f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (IgusaScheme.chartAlgFin N q).val v f).symm
  letI iQXF : Algebra ℚ[X] (FF N) := (Polynomial.aeval vF).toRingHom.toAlgebra
  letI iQXK : Algebra ℚ[X] ↥ℚ⟮vF⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ vF)).toRingHom.toAlgebra
  letI iRXK : Algebra (Rq q)[X] ↥ℚ⟮vF⟯ := ((algebraMap ℚ[X] ↥ℚ⟮vF⟯).comp (algebraMap (Rq q)[X] ℚ[X])).toAlgebra
  haveI tRQK : IsScalarTower (Rq q)[X] ℚ[X] ↥ℚ⟮vF⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI tQKF : IsScalarTower ℚ[X] ↥ℚ⟮vF⟯ (FF N) := IsScalarTower.of_algebraMap_eq fun f => by
    change Polynomial.aeval vF f = ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ vF) f : ↥ℚ⟮vF⟯) : FF N)
    exact Polynomial.aeval_algHom_apply (ℚ⟮vF⟯).val (IntermediateField.AdjoinSimple.gen ℚ vF) f
  haveI tRQF : IsScalarTower (Rq q)[X] ℚ[X] (FF N) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF]
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap (Rq q) ℚ) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI tRKF : IsScalarTower (Rq q)[X] ↥ℚ⟮vF⟯ (FF N) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [IsScalarTower.algebraMap_apply (Rq q)[X] ℚ[X] (FF N), IsScalarTower.algebraMap_apply ℚ[X] ↥ℚ⟮vF⟯ (FF N)]
    rfl

  haveI : IsLocalization ((nonZeroDivisors (Rq q)).map (C : Rq q →+* (Rq q)[X])) ℚ[X] := Polynomial.isLocalization _ ℚ
  haveI : IsFractionRing ℚ[X] ↥ℚ⟮vF⟯ := isFractionRing_polynomial_adjoin N vF hvt
  haveI : Algebra.FormallyUnramified (Rq q)[X] ℚ[X] :=
    Algebra.FormallyUnramified.of_isLocalization ((nonZeroDivisors (Rq q)).map (C : Rq q →+* (Rq q)[X]))
  haveI : Algebra.FormallyUnramified ℚ[X] ↥ℚ⟮vF⟯ :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℚ[X])
  haveI : Algebra.FormallyUnramified (Rq q)[X] ↥ℚ⟮vF⟯ := Algebra.FormallyUnramified.comp (Rq q)[X] ℚ[X] ↥ℚ⟮vF⟯
  haveI : Algebra.IsAlgebraic ↥ℚ⟮vF⟯ (FF N) := isAlgebraic_adjoin_simple N vF hvt
  haveI : Algebra.FormallyUnramified ↥ℚ⟮vF⟯ (FF N) := Algebra.FormallyUnramified.of_isSeparable ↥ℚ⟮vF⟯ (FF N)
  haveI : Algebra.FormallyUnramified (Rq q)[X] (FF N) := Algebra.FormallyUnramified.comp (Rq q)[X] ↥ℚ⟮vF⟯ (FF N)

  haveI : Algebra.FiniteType (Rq q) (AF N q) := (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N q).1
  haveI : IsScalarTower (Rq q) (Rq q)[X] (AF N q) := IsScalarTower.of_algebraMap_eq fun n => by
    change algebraMap (Rq q) (AF N q) n = Polynomial.aeval v (algebraMap (Rq q) (Rq q)[X] n)
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI : Algebra.FiniteType (Rq q)[X] (AF N q) := Algebra.FiniteType.of_restrictScalars_finiteType (Rq q) (Rq q)[X] (AF N q)
  haveI : IsFractionRing (AF N q) (FF N) := isFractionRing_chartAlgFin N q

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_smul_kaehler_eq_zero (R := (Rq q)[X]) (A := AF N q) (FF N)

  letI jA : Algebra ℤ[X] (AF N q) := (Polynomial.aeval (R := ℤ) v).toRingHom.toAlgebra
  letI jF : Algebra ℤ[X] (FF N) := ((algebraMap (AF N q) (FF N)).comp (algebraMap ℤ[X] (AF N q))).toAlgebra
  haveI uAF : IsScalarTower ℤ[X] (AF N q) (FF N) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF' : ∀ f : ℤ[X], algebraMap ℤ[X] (FF N) f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (IgusaScheme.chartAlgFin N q).val.toRingHom.toIntAlgHom v f).symm
  haveI uZQF : IsScalarTower ℤ[X] ℚ[X] (FF N) := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF']
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap ℤ ℚ) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) ℚ[X] := Polynomial.isLocalization _ ℚ
  have haalg : IsAlgebraic ℤ[X] a := by
    have h1 : IsAlgebraic ↥ℚ⟮vF⟯ (a : FF N) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℚ[X] (a : FF N) := (IsFractionRing.isAlgebraic_iff ℚ[X] ↥ℚ⟮vF⟯ (FF N)).mpr h1
    haveI : Algebra.IsAlgebraic ℤ[X] ℚ[X] :=
      IsLocalization.isAlgebraic ℚ[X] ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X]))
    have h3 : IsAlgebraic ℤ[X] (a : FF N) := h2.restrictScalars ℤ[X]
    exact (isAlgebraic_algebraMap_iff (R := ℤ[X]) (S := AF N q) (A := FF N) Subtype.val_injective).mp h3
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_algebraMap_mem_span ha0 haalg
  refine ⟨c, hc0, fun P _ _ hcP => ?_⟩
  exact isUnramifiedAt_of_forall_smul_eq_zero ha P fun haP => hcP ((Ideal.span_singleton_le_iff_mem P).mpr haP hc)

end ModularCurve.DRModelPackageLevel.OggUnramLevelAux
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.DRModelPackageLevel P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.DRModelPackageLevel.OggUnramLevelAux"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.DRModelPackageLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.DRModelPackageLevel P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve.DRModelPackageLevel.OggUnramLevelAux"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    letI : Algebra (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := (Polynomial.aeval (R := R q) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [P.IsPrime],
      P.comap (algebraMap (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt (R q)[X] P :=
  ModularCurve.DRModelPackageLevel.OggUnramLevelAux.main (N₀ * q) q v hv

end S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem (solution)
