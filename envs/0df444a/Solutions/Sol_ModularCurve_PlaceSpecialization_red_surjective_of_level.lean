-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.red_surjective_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c12191a8-8183-5c08-aa8c-d86408264fa6

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_ModularCurve_jqNModC_mul_pow_eq_pow
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_isSeparable_jqNModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_red_surjective_of_level
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

private theorem redlev_ne_zero_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {x : F} (hx : v.ord x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hx (AlgebraicCurve.Place.ord_zero v)

private theorem redlev_ord_sub_algebraMap_of_neg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {x : F} (hx : v.ord x < 0) (b : K) :
    v.ord (x - algebraMap K F b) = v.ord x := by
  by_cases hb : b = 0
  · subst hb
    simp
  · have hx0 : x ≠ 0 := redlev_ne_zero_of_ord_ne_zero v hx.ne
    have hg : algebraMap K F (-b) ≠ 0 := (map_ne_zero (algebraMap K F)).mpr (neg_ne_zero.mpr hb)
    have hlt : v.ord x < v.ord (algebraMap K F (-b)) := by
      rw [AlgebraicCurve.Place.ord_algebraMap]
      exact hx
    rw [sub_eq_add_neg, ← map_neg (algebraMap K F)]
    exact AlgebraicCurve.Place.ord_add_eq_of_lt v hx0 hg hlt

private theorem redlev_eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {x : F} {b c : K} (hb : 0 < v.ord (x - algebraMap K F b))
    (hc : 0 < v.ord (x - algebraMap K F c)) : c = b := by
  by_contra hne
  have hd : algebraMap K F (b - c) ≠ 0 :=
    (map_ne_zero (algebraMap K F)).mpr (sub_ne_zero.mpr fun h => hne h.symm)
  have hg : x - algebraMap K F b ≠ 0 := redlev_ne_zero_of_ord_ne_zero v hb.ne'
  have hlt : v.ord (algebraMap K F (b - c)) < v.ord (x - algebraMap K F b) := by
    rw [AlgebraicCurve.Place.ord_algebraMap]
    exact hb
  have h := AlgebraicCurve.Place.ord_add_eq_of_lt v hd hg hlt
  rw [AlgebraicCurve.Place.ord_algebraMap] at h
  have hsum : algebraMap K F (b - c) + (x - algebraMap K F b) = x - algebraMap K F c := by
    rw [map_sub]
    ring
  rw [hsum] at h
  omega

private theorem redlev_exists_pos_of_degree_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : AlgebraicCurve.Divisor K F) (hdeg : AlgebraicCurve.Divisor.degree D = 0)
    {v₀ : AlgebraicCurve.Place K F} (hneg : D v₀ < 0) (hv₀ : v₀.deg = 1) :
    ∃ v : AlgebraicCurve.Place K F, 0 < D v := by
  classical
  by_contra hall
  have hnonpos : ∀ v : AlgebraicCurve.Place K F, D v * (v.deg : ℤ) ≤ 0 := fun v => by
    have h1 : D v ≤ 0 := not_lt.mp fun h => hall ⟨v, h⟩
    have h2 : (0 : ℤ) ≤ (v.deg : ℤ) := Nat.cast_nonneg _
    nlinarith
  have hsum : AlgebraicCurve.Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
    simp [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hneg.ne
  have hsplit : D v₀ * (v₀.deg : ℤ) + ∑ v ∈ D.support.erase v₀, D v * (v.deg : ℤ)
      = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
    Finset.add_sum_erase D.support (fun v => D v * (v.deg : ℤ)) hmem
  have hrest : ∑ v ∈ D.support.erase v₀, D v * (v.deg : ℤ) ≤ 0 :=
    Finset.sum_nonpos fun v _ => hnonpos v
  rw [hv₀, Nat.cast_one, mul_one] at hsplit
  rw [hsum] at hdeg
  omega

private theorem redlev_isSeparable_jqNModC (q : ℕ) [hq : Fact q.Prime] (N : ℕ) [NeZero N]
    (k : Type*) [Field k] [CharP k q] :
    IsSeparable (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))) (jqNModC k N) := by
  obtain ⟨e, M, hM, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) q hq.out.one_lt.ne'
  haveI : NeZero M := ⟨by
    rintro rfl
    rw [mul_zero] at hN
    exact NeZero.ne N hN⟩
  have hMk : (M : k) ≠ 0 := fun h => hM ((CharP.cast_eq_zero_iff k q M).mp h)
  have hsepM := isSeparable_jqNModC_of_natCast_ne_zero k M hMk
  have hN' : N = M * q ^ e := by rw [hN, mul_comm]
  subst hN'
  rw [jqNModC_mul_pow_eq_pow k M (ℓ := q) e]
  haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
    (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))) (LaurentSeries k)).mpr hsepM
  exact IntermediateField.isSeparable_of_mem_isSeparable
    (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))) (LaurentSeries k)
    (pow_mem (IntermediateField.mem_adjoin_simple_self
      (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))) (jqNModC k M)) (q ^ e))

private theorem redlev_exists_place_ord_pos (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N]
    (k : Type*) [Field k] [CharP k q] (b : k) :
    ∃ v : AlgebraicCurve.Place k (modularFunctionFieldC k N),
      0 < v.ord (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) b) := by
  have hpd : HasPrincipalDivisors k (modularFunctionFieldC k N) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_isSeparable_jqNModC k N
      (redlev_isSeparable_jqNModC q N k)
  have hj := ord_cuspInftyGeom_jq k N
  have hneg := hj.trans_lt (by omega : (-1 : ℤ) < 0)
  have hcusp := (redlev_ord_sub_algebraMap_of_neg (cuspInftyGeom k N) hneg b).trans hj
  have hf0 := redlev_ne_zero_of_ord_ne_zero (cuspInftyGeom k N) (hcusp.trans_ne (by omega))
  obtain ⟨D, hD, hdeg⟩ := hpd.exists_divisor _ hf0
  have hDc : D (cuspInftyGeom k N) < 0 := by
    rw [hD, hcusp]
    omega
  obtain ⟨v, hv⟩ := redlev_exists_pos_of_degree_eq_zero D hdeg hDc (deg_cuspInftyGeom k N)
  refine ⟨v, ?_⟩
  rw [hD v] at hv
  exact hv

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) : Function.Surjective red := by
  intro b
  obtain ⟨v, hv⟩ := redlev_exists_place_ord_pos q N k b
  obtain ⟨w, rfl⟩ := P.d4 v
  by_contra hne
  have hpole := P.d0_j_pole w fun a => by
    by_contra hlt
    exact hne ⟨a, redlev_eq_of_ord_sub_pos (P.sp w) hv (P.d0_j w a (not_le.mp hlt))⟩
  rw [redlev_ord_sub_algebraMap_of_neg (P.sp w) hpole b] at hv
  exact absurd hpole (not_lt.mpr hv.le)

end S_ModularCurve_PlaceSpecialization_red_surjective_of_level
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_red_surjective_of_level (solution)
