-- Prove2me | solution 1 for ModularCurve.XOneP.exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bf88fece-6626-55a6-b7e3-dc34e79b6260

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section

open scoped Polynomial TensorProduct IntermediateField
open Polynomial IsLocalRing

namespace ECL_N1UNRGEN

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

variable {k : Type*} [Field k]

private theorem order_pow_eq (z : LaurentSeries k) (hz : z ≠ 0) : ∀ n : ℕ, z ^ n ≠ 0 ∧ (z ^ n).order = n * z.order
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hn, hon⟩ := order_pow_eq z hz n
    refine ⟨mul_ne_zero hn hz, ?_⟩
    rw [pow_succ, HahnSeries.order_mul hn hz, hon]
    push_cast
    ring

private theorem aeval_ne_zero_of_order_neg {z : LaurentSeries k} (hz : z ≠ 0) (hneg : z.order < 0)
    (g : k[X]) (hg : g.Monic) (hD : 0 < g.natDegree) : aeval z g ≠ 0 := by
  classical
  obtain ⟨hzD, hoD⟩ := order_pow_eq z hz g.natDegree

  have key : ∀ i : ℕ, (algebraMap k (LaurentSeries k) (g.coeff i) * z ^ i).coeff (g.natDegree * z.order) =
      g.coeff i * (z ^ i).coeff (g.natDegree * z.order) := by
    intro i
    rw [HahnSeries.algebraMap_apply', show algebraMap k (PowerSeries k) (g.coeff i) = PowerSeries.C (g.coeff i) from rfl,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

  have hcoeff : (aeval z g).coeff (g.natDegree * z.order) = (z ^ g.natDegree).coeff (g.natDegree * z.order) := by
    rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ, key, Finset.sum_eq_zero ?hlow, zero_add,
      show g.coeff g.natDegree = 1 from hg, one_mul]
    intro i hi
    rw [Finset.mem_range] at hi
    rw [key]
    obtain ⟨hzi, hoi⟩ := order_pow_eq z hz i
    have hlt : (g.natDegree : ℤ) * z.order < (z ^ i).order := by
      rw [hoi]
      have : (i : ℤ) < g.natDegree := by exact_mod_cast hi
      nlinarith
    rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]
  have hne : (z ^ g.natDegree).coeff (g.natDegree * z.order) ≠ 0 := by
    rw [← hoD]; exact (HahnSeries.coeff_order_eq_zero.not.2 hzD)
  intro h
  rw [h, HahnSeries.coeff_zero] at hcoeff
  exact hne hcoeff.symm

private theorem order_eq_of_coeff {z : LaurentSeries k} {m : ℤ} (h1 : z.coeff m ≠ 0) (h2 : ∀ n < m, z.coeff n = 0) :
    z.order = m := by
  have hz : z ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push_neg at hlt
  exact (HahnSeries.coeff_order_eq_zero.not.2 hz) (h2 _ hlt)

private theorem transcendental_of_order_neg {z : LaurentSeries k} (hz : z ≠ 0) (hneg : z.order < 0) :
    Transcendental k z := by
  classical
  rintro ⟨P, hP0, hP⟩
  set g : k[X] := P * C (P.leadingCoeff)⁻¹ with hg
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hgm : g.Monic := by
    rw [Monic, hg, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀ hlc]
  have hgz : aeval z g = 0 := by rw [hg, map_mul, hP, zero_mul]
  by_cases hD : 0 < g.natDegree
  · exact aeval_ne_zero_of_order_neg hz hneg g hgm hD hgz
  · have h0 : g.natDegree = 0 := Nat.eq_zero_of_not_pos hD
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, aeval_C, show g.coeff 0 = 1 by
      have := hgm; rw [Monic, leadingCoeff, h0] at this; exact this, map_one] at hgz
    exact one_ne_zero hgz

end Laurent

section FunctionField

variable (L : Type) [Field L] (F : Type) [Field F] [Algebra L F]

attribute [local instance 10000] RatFunc.instAlgebraOfPolynomial in
theorem isFractionRing_polynomial_adjoin (x : F) (hx : Transcendental L x) :
    letI : Algebra L[X] ↥L⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen L x)).toRingHom.toAlgebra
    IsFractionRing L[X] ↥L⟮x⟯ := by
  letI : Algebra L[X] ↥L⟮x⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen L x)).toRingHom.toAlgebra
  obtain ⟨e, he⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental L F x hx
  have halg : ∀ f : L[X], algebraMap L[X] (RatFunc L) f = aeval RatFunc.X f := fun f => by
    have h1 := aeval_algHom_apply (IsScalarTower.toAlgHom L L[X] (RatFunc L)) X f
    rw [aeval_X_left, AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_X] at h1
    exact h1.symm
  have hcomm : ∀ f : L[X], e.symm.toRingEquiv (algebraMap L[X] (RatFunc L) f) = algebraMap L[X] ↥L⟮x⟯ f := by
    intro f
    change e.symm.toRingEquiv (algebraMap L[X] (RatFunc L) f) = aeval (IntermediateField.AdjoinSimple.gen L x) f
    rw [halg, AlgEquiv.coe_ringEquiv, ← aeval_algHom_apply, ← he, AlgEquiv.symm_apply_apply]
    rfl
  let e' : RatFunc L ≃ₐ[L[X]] ↥L⟮x⟯ := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) hcomm
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors L[X]) e'

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isAlgebraic_adjoin_simple (j : F) [FiniteDimensional ↥L⟮j⟯ F] (x : F) (hx : Transcendental L x) :
    Algebra.IsAlgebraic ↥L⟮x⟯ F := by
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin L ({j} : Set F)) F :=
    Algebra.IsAlgebraic.trans (R := ↥(Algebra.adjoin L ({j} : Set F))) (S := ↥L⟮j⟯) (A := F)
  have htr : Algebra.trdeg L F ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk L ({j} : Set F)
    rwa [Cardinal.mk_singleton] at h
  have h1 : AlgebraicIndependent L ![x] := algebraicIndependent_iff_transcendental.mpr hx
  have hb : IsTranscendenceBasis L ![x] := h1.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have h := hb.isAlgebraic_field
  have hr : Set.range ![x] = {x} := by simp
  rwa [hr] at h

end FunctionField

section Main

open AlgebraicCurve.TwoChartIntegralModel

variable (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)

omit [CharZero L] [Algebra.IsAlgebraic ℚ L] [Fact (j ≠ 0)] in

theorem transcendental_of_coe {x : ↥K} (hx : Transcendental L (x : LaurentSeries L)) : Transcendental L x := by
  intro halg
  apply hx
  obtain ⟨P, hP0, hP⟩ := halg
  refine ⟨P, hP0, ?_⟩
  have h := congrArg (algebraMap ↥K (LaurentSeries L)) hP
  rwa [map_zero, ← aeval_algebraMap_apply] at h

attribute [local instance] Polynomial.algebra in
set_option maxHeartbeats 6400000 in
theorem main (htj : Transcendental A j) (hFD : FiniteDimensional ↥L⟮j⟯ ↥K)
    (v : 𝒪) (hvt : Transcendental L (v : ↥K)) :
    letI : Algebra A[X] 𝒪 := (Polynomial.aeval (R := A) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal 𝒪) [P.IsPrime],
      P.comap (algebraMap A 𝒪) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt A[X] P := by
  set vF : ↥K := (v : ↥K) with hvF
  haveI := hFD

  letI iA : Algebra A[X] 𝒪 := (Polynomial.aeval (R := A) v).toRingHom.toAlgebra
  letI iF : Algebra A[X] ↥K := ((algebraMap 𝒪 ↥K).comp (algebraMap A[X] 𝒪)).toAlgebra
  haveI tAF : IsScalarTower A[X] 𝒪 ↥K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF : ∀ f : A[X], algebraMap A[X] ↥K f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val v f).symm
  letI iQXF : Algebra L[X] ↥K := (Polynomial.aeval vF).toRingHom.toAlgebra
  letI iQXK : Algebra L[X] ↥L⟮vF⟯ := (Polynomial.aeval (IntermediateField.AdjoinSimple.gen L vF)).toRingHom.toAlgebra
  letI iRXK : Algebra A[X] ↥L⟮vF⟯ := ((algebraMap L[X] ↥L⟮vF⟯).comp (algebraMap A[X] L[X])).toAlgebra
  haveI tRQK : IsScalarTower A[X] L[X] ↥L⟮vF⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI tQKF : IsScalarTower L[X] ↥L⟮vF⟯ ↥K := IsScalarTower.of_algebraMap_eq fun f => by
    change Polynomial.aeval vF f = ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen L vF) f : ↥L⟮vF⟯) : ↥K)
    exact Polynomial.aeval_algHom_apply (L⟮vF⟯).val (IntermediateField.AdjoinSimple.gen L vF) f
  haveI tRQF : IsScalarTower A[X] L[X] ↥K := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF]
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap A L) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI tRKF : IsScalarTower A[X] ↥L⟮vF⟯ ↥K := IsScalarTower.of_algebraMap_eq fun f => by
    rw [IsScalarTower.algebraMap_apply A[X] L[X] ↥K, IsScalarTower.algebraMap_apply L[X] ↥L⟮vF⟯ ↥K]
    rfl

  haveI : IsLocalization ((nonZeroDivisors A).map (C : A →+* A[X])) L[X] := Polynomial.isLocalization _ L
  haveI : IsFractionRing L[X] ↥L⟮vF⟯ := isFractionRing_polynomial_adjoin L ↥K vF hvt
  haveI : Algebra.FormallyUnramified A[X] L[X] :=
    Algebra.FormallyUnramified.of_isLocalization ((nonZeroDivisors A).map (C : A →+* A[X]))
  haveI : Algebra.FormallyUnramified L[X] ↥L⟮vF⟯ :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors L[X])
  haveI : Algebra.FormallyUnramified A[X] ↥L⟮vF⟯ := Algebra.FormallyUnramified.comp A[X] L[X] ↥L⟮vF⟯
  haveI : Algebra.IsAlgebraic ↥L⟮vF⟯ ↥K := isAlgebraic_adjoin_simple L ↥K j vF hvt
  haveI : Algebra.FormallyUnramified ↥L⟮vF⟯ ↥K := Algebra.FormallyUnramified.of_isSeparable ↥L⟮vF⟯ ↥K
  haveI : Algebra.FormallyUnramified A[X] ↥K := Algebra.FormallyUnramified.comp A[X] ↥L⟮vF⟯ ↥K

  haveI hsep : Algebra.IsSeparable ↥L⟮j⟯ ↥K := Algebra.IsSeparable.of_integral _ _
  haveI : Algebra.FiniteType A 𝒪 :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L ↥K j htj hFD hsep).1
  haveI : IsScalarTower A A[X] 𝒪 := IsScalarTower.of_algebraMap_eq fun n => by
    change algebraMap A 𝒪 n = Polynomial.aeval v (algebraMap A A[X] n)
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI : Algebra.FiniteType A[X] 𝒪 := Algebra.FiniteType.of_restrictScalars_finiteType A A[X] 𝒪
  haveI : Algebra.IsAlgebraic ↥L⟮j⟯ ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsFractionRing 𝒪 ↥K :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L ↥K ({j} : Set ↥K)

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_smul_kaehler_eq_zero (R := A[X]) (A := 𝒪) ↥K

  letI jA : Algebra ℤ[X] 𝒪 := (Polynomial.aeval (R := ℤ) v).toRingHom.toAlgebra
  letI jF : Algebra ℤ[X] ↥K := ((algebraMap 𝒪 ↥K).comp (algebraMap ℤ[X] 𝒪)).toAlgebra
  haveI uAF : IsScalarTower ℤ[X] 𝒪 ↥K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgF' : ∀ f : ℤ[X], algebraMap ℤ[X] ↥K f = Polynomial.aeval vF f := fun f =>
    (Polynomial.aeval_algHom_apply (ModularCurve.TwoChart.chartAlgFin A (↥K) j).val.toRingHom.toIntAlgHom v f).symm
  haveI uZQF : IsScalarTower ℤ[X] L[X] ↥K := IsScalarTower.of_algebraMap_eq fun f => by
    rw [halgF']
    change Polynomial.aeval vF f = Polynomial.aeval vF (Polynomial.mapRingHom (algebraMap ℤ L) f)
    rw [Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
  haveI : Algebra.IsAlgebraic ℤ L :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩
  have haalg : IsAlgebraic ℤ[X] a := by
    have h1 : IsAlgebraic ↥L⟮vF⟯ (a : ↥K) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic L[X] (a : ↥K) := (IsFractionRing.isAlgebraic_iff L[X] ↥L⟮vF⟯ ↥K).mpr h1
    have h3 : IsAlgebraic ℤ[X] (a : ↥K) := h2.restrictScalars ℤ[X]
    exact (isAlgebraic_algebraMap_iff (R := ℤ[X]) (S := 𝒪) (A := ↥K) Subtype.val_injective).mp h3
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_algebraMap_mem_span ha0 haalg
  refine ⟨c, hc0, fun P _ _ hcP => ?_⟩
  exact isUnramifiedAt_of_forall_smul_eq_zero ha P fun haP => hcP ((Ideal.span_singleton_le_iff_mem P).mpr haP hc)

end Main

section GenUnramS

variable {R : Type} [CommRing R] [IsDomain R] [CharZero R]
variable {A : Type} [CommRing A] [IsDomain A] [Algebra R A]

private theorem dvd_of_irreducible_of_rootS {k K : Type*} [Field k] [Field K] [Algebra k K] {q r : k[X]}
    (hq : Irreducible q) {β : K} (hqβ : aeval β q = 0) (hrβ : aeval β r = 0) : q ∣ r := by
  have hmin : minpoly k β ∣ q := minpoly.dvd k β hqβ
  have hint : IsIntegral k β := ⟨q * C q.leadingCoeff⁻¹, by
    refine ⟨?_, ?_⟩
    · rw [Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀ (leadingCoeff_ne_zero.2 hq.ne_zero)]
    · rw [eval₂_mul, ← aeval_def, hqβ, zero_mul]⟩
  exact ((minpoly.irreducible hint).associated_of_dvd hq hmin).symm.dvd.trans (minpoly.dvd k β hrβ)

private theorem aeval_notMem_of_not_dvdS (v : A) (g c₀ : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) (hndvd : ¬ g ∣ c₀) (P : Ideal A) [P.IsPrime]
    (hP : P.comap (algebraMap R A) = ⊥) (hgP : aeval v g ∈ P) : aeval v c₀ ∉ P := by
  intro hc
  let L := FractionRing (A ⧸ P)
  haveI : CharZero (A ⧸ P) := by
    refine charZero_of_inj_zero (fun n hn => ?_)
    have h1 : algebraMap R A n ∈ P := by
      rw [map_natCast, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn
    have h2 : (n : R) ∈ P.comap (algebraMap R A) := h1
    rw [hP, Ideal.mem_bot] at h2
    exact_mod_cast h2
  haveI : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (A ⧸ P) L)
  letI : Algebra ℚ L := DivisionRing.toRatAlgebra
  let β : L := algebraMap (A ⧸ P) L (Ideal.Quotient.mk P v)
  have hroot : ∀ f : ℤ[X], aeval v f ∈ P → aeval β (f.map (Int.castRingHom ℚ)) = 0 := by
    intro f hf
    have hT := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := L) (Subsingleton.elim _ _)
    haveI := hT
    have e1 : aeval β (f.map (Int.castRingHom ℚ)) = aeval β f := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]
    have e2 : aeval β f = algebraMap (A ⧸ P) L (aeval (Ideal.Quotient.mk P v) f) := aeval_algebraMap_apply L _ f
    have e3 : aeval (Ideal.Quotient.mk P v) f = Ideal.Quotient.mk P (aeval v f) := by
      rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply]
    rw [e1, e2, e3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hdvd : g.map (Int.castRingHom ℚ) ∣ c₀.map (Int.castRingHom ℚ) :=
    dvd_of_irreducible_of_rootS hirr (hroot g hgP) (hroot c₀ hc)
  rw [Polynomial.map_dvd_map (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int hg] at hdvd
  exact hndvd hdvd

private theorem formallyUnramified_of_surjectiveS {R' X Y : Type*} [CommRing R'] [CommRing X] [CommRing Y] [Algebra R' X]
    [Algebra R' Y] (f : X →+* Y) (hf : Function.Surjective f) (hcomm : f.comp (algebraMap R' X) = algebraMap R' Y)
    [Algebra.FormallyUnramified R' X] : Algebra.FormallyUnramified R' Y :=
  Algebra.FormallyUnramified.of_surjective ({ f with commutes' := fun r => RingHom.congr_fun hcomm r } : X →ₐ[R'] Y) hf

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem isUnramifiedAt_of_comap_eq_botS (L : Type) [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
    (v : A) (g c₀ : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) (hndvd : ¬ g ∣ c₀)
    (hunr : letI : Algebra R[X] A := (aeval (R := R) v).toRingHom.toAlgebra
      ∀ (P : Ideal A) [P.IsPrime], P.comap (algebraMap R A) = ⊥ → aeval v c₀ ∉ P → Algebra.IsUnramifiedAt R[X] P)
    (S : Type) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (hsurj : Function.Surjective (algebraMap A S)) (hgS : algebraMap A S (aeval v g) = 0)
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = ⊥) :
    Algebra.IsUnramifiedAt R q := by
  classical
  letI iRX : Algebra R[X] A := (aeval (R := R) v).toRingHom.toAlgebra
  letI iRXS : Algebra R[X] S := ((algebraMap A S).comp (algebraMap R[X] A)).toAlgebra
  haveI : IsScalarTower R[X] A S := IsScalarTower.of_algebraMap_eq' rfl
  let B := S
  let f : A →+* S := algebraMap A S
  let P : Ideal A := q.comap f
  haveI : P.IsPrime := Ideal.comap_isPrime f q

  have hPR : P.comap (algebraMap R A) = ⊥ := by
    refine le_bot_iff.1 (fun r hr => ?_)
    rw [Ideal.mem_comap, Ideal.mem_comap] at hr
    have h1 : f (algebraMap R A r) = algebraMap R B r := (IsScalarTower.algebraMap_apply R A S r).symm
    rw [h1, ← Ideal.mem_comap, hq] at hr
    exact hr

  have hgP : aeval v g ∈ P := by
    show f (aeval v g) ∈ q
    have : f (aeval v g) = 0 := hgS
    rw [this]; exact q.zero_mem

  have hcP : aeval v c₀ ∉ P := aeval_notMem_of_not_dvdS (R := R) v g c₀ hg hirr hndvd P hPR hgP
  have hUP : Algebra.IsUnramifiedAt R[X] P := hunr P hPR hcP

  have hPq : P = q.comap f := rfl
  let ψ : Localization.AtPrime P →+* Localization.AtPrime q := Localization.localRingHom P q f hPq
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨s, t⟩, hz⟩ := IsLocalization.surj q.primeCompl z
    obtain ⟨a, rfl⟩ := hsurj s
    obtain ⟨b, hb⟩ := hsurj (t : B)
    have hbP : b ∉ P := by
      intro h
      apply t.2
      show (t : B) ∈ q
      rw [← hb]; exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) a (⟨b, hbP⟩ : P.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk', eq_comm, IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk]
    simp only at hz
    show z * algebraMap B (Localization.AtPrime q) (f b) = algebraMap B (Localization.AtPrime q) (f a)
    rw [show f b = (t : B) from hb]
    exact hz

  have halgS : algebraMap R[X] (Localization.AtPrime q) =
      (algebraMap B (Localization.AtPrime q)).comp (f.comp (algebraMap R[X] A)) := by
    rw [IsScalarTower.algebraMap_eq R[X] B (Localization.AtPrime q), IsScalarTower.algebraMap_eq R[X] A B]
  have hC : ∀ r : R, algebraMap R[X] (Localization.AtPrime q) (C r) = algebraMap R (Localization.AtPrime q) r := by
    intro r
    rw [halgS, RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply R B (Localization.AtPrime q)]
    show algebraMap B _ (f ((aeval (R := R) v).toRingHom (C r))) = algebraMap B _ (algebraMap R B r)
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
    congr 1
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  have hcomm : ψ.comp (algebraMap R[X] (Localization.AtPrime P)) = algebraMap R[X] (Localization.AtPrime q) := by
    rw [halgS, IsScalarTower.algebraMap_eq R[X] A (Localization.AtPrime P)]
    refine RingHom.ext (fun r => ?_)
    simp only [RingHom.comp_apply]
    exact Localization.localRingHom_to_map P q f hPq _
  haveI hU1 : Algebra.FormallyUnramified R[X] (Localization.AtPrime q) :=
    formallyUnramified_of_surjectiveS ψ hψ hcomm

  have hunitR : ∀ y : nonZeroDivisors R, IsUnit (algebraMap R (Localization.AtPrime q) y) := by
    intro y
    have hy : (y : R) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime q)]
    refine IsLocalization.map_units (Localization.AtPrime q) (⟨_, ?_⟩ : q.primeCompl)
    intro hmem
    have : (y : R) ∈ q.comap (algebraMap R B) := hmem
    rw [hq, Ideal.mem_bot] at this
    exact hy this
  let i : L →+* Localization.AtPrime q := IsLocalization.lift (M := nonZeroDivisors R) hunitR
  have hi : i.comp (algebraMap R L) = algebraMap R (Localization.AtPrime q) :=
    IsLocalization.lift_comp (M := nonZeroDivisors R) hunitR
  letI iL : Algebra L (Localization.AtPrime q) := i.toAlgebra
  letI iQ : Algebra ℚ (Localization.AtPrime q) := (i.comp (algebraMap ℚ L)).toAlgebra
  haveI hTQL : IsScalarTower ℚ L (Localization.AtPrime q) := IsScalarTower.of_algebraMap_eq' rfl
  let gQ : ℚ[X] := g.map (Int.castRingHom ℚ)
  haveI : Fact (Irreducible gQ) := ⟨hirr⟩
  let x : Localization.AtPrime q := algebraMap R[X] (Localization.AtPrime q) X
  have hgx : eval₂ (algebraMap ℚ (Localization.AtPrime q)) x gQ = 0 := by

    let Φ : ℤ[X] →+* Localization.AtPrime q := eval₂RingHom ((algebraMap ℚ (Localization.AtPrime q)).comp (Int.castRingHom ℚ)) x
    let Ψ : ℤ[X] →+* Localization.AtPrime q := (algebraMap R[X] (Localization.AtPrime q)).comp (mapRingHom (Int.castRingHom R))
    have hΦΨ : Φ = Ψ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      show eval₂ ((algebraMap ℚ (Localization.AtPrime q)).comp (Int.castRingHom ℚ)) x X =
        algebraMap R[X] (Localization.AtPrime q) (Polynomial.map (Int.castRingHom R) X)
      rw [eval₂_X, Polynomial.map_X]
    have e1 : eval₂ (algebraMap ℚ (Localization.AtPrime q)) x gQ = Φ g := by
      show eval₂ _ x (g.map (Int.castRingHom ℚ)) = eval₂ ((algebraMap ℚ (Localization.AtPrime q)).comp (Int.castRingHom ℚ)) x g
      rw [Polynomial.eval₂_map]
    rw [e1, hΦΨ]
    show algebraMap R[X] (Localization.AtPrime q) (g.map (Int.castRingHom R)) = 0
    rw [halgS, RingHom.comp_apply, RingHom.comp_apply]
    have hgA : algebraMap R[X] A (g.map (Int.castRingHom R)) = aeval v g := by
      show (aeval (R := R) v).toRingHom (g.map (Int.castRingHom R)) = aeval v g
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, show Int.castRingHom R = algebraMap ℤ R from rfl,
        aeval_map_algebraMap]
    rw [hgA, show f (aeval v g) = 0 from hgS, map_zero]
  let K := AdjoinRoot gQ
  have hgx' : gQ.eval₂ (↑(Algebra.ofId ℚ (Localization.AtPrime q)) : ℚ →+* Localization.AtPrime q) x = 0 := hgx
  let φK : K →ₐ[ℚ] Localization.AtPrime q := AdjoinRoot.liftAlgHom gQ (Algebra.ofId ℚ (Localization.AtPrime q)) x hgx'

  let KL := L ⊗[ℚ] K
  let ψ : KL →ₐ[L] Localization.AtPrime q :=
    Algebra.TensorProduct.lift (Algebra.ofId L (Localization.AtPrime q)) φK (fun a b => Commute.all _ _)
  letI iKL : Algebra KL (Localization.AtPrime q) := ψ.toRingHom.toAlgebra

  letI algRK : Algebra R[X] KL :=
    (eval₂RingHom ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := L) (B := K)).comp (algebraMap R L))
      ((1 : L) ⊗ₜ[ℚ] AdjoinRoot.root gQ)).toAlgebra
  have hψleft : ∀ a : L, ψ (a ⊗ₜ[ℚ] (1 : K)) = i a := by
    intro a
    show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[ℚ] (1 : K)) = i a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hψroot : ψ ((1 : L) ⊗ₜ[ℚ] AdjoinRoot.root gQ) = x := by
    show Algebra.TensorProduct.lift _ _ _ ((1 : L) ⊗ₜ[ℚ] AdjoinRoot.root gQ) = x
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact AdjoinRoot.liftAlgHom_root gQ _ x hgx'
  have hTK : IsScalarTower R[X] KL (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · rw [hC, RingHom.comp_apply]
      show algebraMap R (Localization.AtPrime q) r =
        ψ (eval₂RingHom ((Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap R L)) ((1 : L) ⊗ₜ[ℚ] AdjoinRoot.root gQ) (C r))
      rw [Polynomial.coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
      show algebraMap R (Localization.AtPrime q) r = ψ (algebraMap R L r ⊗ₜ[ℚ] (1 : K))
      rw [hψleft]
      exact (RingHom.congr_fun hi r).symm
    · rw [RingHom.comp_apply]
      show x = ψ (eval₂RingHom ((Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap R L)) ((1 : L) ⊗ₜ[ℚ] AdjoinRoot.root gQ) X)
      rw [Polynomial.coe_eval₂RingHom, eval₂_X, hψroot]
  haveI := hTK
  haveI hU2 : Algebra.FormallyUnramified KL (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R[X] KL _

  haveI : Module.Finite ℚ K := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hU3 : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI hU3L : Algebra.FormallyUnramified L KL := inferInstance
  haveI hU4 : Algebra.FormallyUnramified R L := Algebra.FormallyUnramified.of_isLocalization (M := nonZeroDivisors R)
  haveI hTRL : IsScalarTower R L KL := TensorProduct.isScalarTower_left
  haveI hU5 : Algebra.FormallyUnramified R KL := Algebra.FormallyUnramified.comp R L KL
  have hT2 : IsScalarTower R KL (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq (R := R) (S := KL) (A := Localization.AtPrime q) (fun r => ?_)
    rw [Algebra.TensorProduct.algebraMap_apply (R := ℚ) (S := R) (A := L) (B := K)]
    show algebraMap R (Localization.AtPrime q) r = ψ (algebraMap R L r ⊗ₜ[ℚ] (1 : K))
    rw [hψleft]
    exact (RingHom.congr_fun hi r).symm
  haveI := hT2
  exact Algebra.FormallyUnramified.comp R KL _

end GenUnramS

end ECL_N1UNRGEN

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)

open ECL_N1UNRGEN in
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
    (v : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hv : ((v : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∨
      ((v : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)
    :
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ g : ℤ[X], g.Monic → Irreducible (g.map (Int.castRingHom ℚ)) → ¬ g ∣ c₀' →
      ∀ (Q : Ideal (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g})) [Q.IsPrime],
        Q.comap (algebraMap A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g})) = ⊥ →
        Algebra.IsUnramifiedAt A Q := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite {p} ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p))
      hT L (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) rfl j hj

  have hz : ((ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p)) : LaurentSeries L).order = 1 - (p : ℤ) := by
    apply order_eq_of_coeff
    · rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_modularUnitSeries_self, map_one]; exact one_ne_zero
    · intro n hn
      rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_modularUnitSeries_of_lt p hn, map_zero]
  have hz0 : ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ≠ 0 := by
    intro h; have := congrArg (fun s : LaurentSeries L => s.coeff (1 - (p : ℤ))) h
    simp only [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_modularUnitSeries_self, map_one, HahnSeries.coeff_zero] at this
    exact one_ne_zero this
  have hut : Transcendental L (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p)) :=
    transcendental_of_order_neg hz0 (by rw [hz]; have := hp.two_le; omega)
  have hvt : Transcendental L (v : ↥K) := by
    apply transcendental_of_coe L K
    rcases hv with hv | hv
    · rw [hv]; exact hut
    · rw [hv]
      intro halg
      apply hut
      haveI : CharZero (LaurentSeries L) :=
        charZero_of_injective_algebraMap (algebraMap L (LaurentSeries L)).injective
      have hpL : ((p : LaurentSeries L) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
      have hmem : (p : LaurentSeries L) ^ 12 * ((p : LaurentSeries L) ^ 12 *
          (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹)⁻¹ ∈ algebraicClosure L (LaurentSeries L) :=
        mul_mem (pow_mem (natCast_mem _ p) 12) (inv_mem (mem_algebraicClosure_iff.mpr halg))
      rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hpL, one_mul] at hmem
      exact mem_algebraicClosure_iff.mp hmem
  obtain ⟨c₀', hc₀', hunr⟩ := ECL_N1UNRGEN.main L K A j htj hFD v hvt
  haveI : CharZero A := (algebraMap A L).charZero
  refine ⟨c₀', hc₀', fun g hg hirr hndvd Q _ hQ => ?_⟩
  exact ECL_N1UNRGEN.isUnramifiedAt_of_comap_eq_botS (R := A) (A := 𝒪) L v g c₀' hg hirr hndvd hunr
    (𝒪 ⧸ Ideal.span {Polynomial.aeval v g}) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) Q hQ

end

end S_ModularCurve_XOneP_exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul (solution)
