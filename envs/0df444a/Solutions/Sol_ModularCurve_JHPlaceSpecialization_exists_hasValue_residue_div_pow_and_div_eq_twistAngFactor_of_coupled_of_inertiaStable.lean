-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_hasValue_residue_div_pow_and_div_eq_twistAngFactor_of_coupled_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2444f720-a50a-5d1b-8370-22fb8b4f981c

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_ModularCurve_JHTwistedDatum
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_hasValue_residue_div_pow_and_div_eq_twistAngFactor_of_coupled_of_inertiaStable

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace AngH

open IsLocalRing

section PlaceLemmas
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

theorem evalAt_eq_of_hasValue {v : Place K F} (hv : v.IsRational) {g : F} {a : K} (h : v.HasValue g a) :
    v.evalAt g = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv h.mem]
  exact h.residue_eq

theorem hasValue_evalAt {v : Place K F} (hv : v.IsRational) {g : F} (hg : g ∈ v.toValuationSubring) :
    v.HasValue g (v.evalAt g) :=
  ⟨hg, (v.algebraMap_evalAt hv hg).symm⟩

theorem hasValue_pow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem hasValue_zpow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) :
    v.HasValue (g ^ n) (a ^ n) := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact hasValue_pow h n
  | negSucc n => rw [zpow_negSucc, zpow_negSucc]; exact (hasValue_pow h (n + 1)).inv (pow_ne_zero _ ha)

theorem ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

theorem ord_prod_zpow (v : Place K F) {ι : Type*} (S : Finset ι) (x : ι → F) (n : ι → ℤ)
    (hx : ∀ i ∈ S, x i ≠ 0) : v.ord (∏ i ∈ S, x i ^ n i) = ∑ i ∈ S, n i * v.ord (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (zpow_ne_zero _ (hx i (Finset.mem_insert_self _ _)))
        (Finset.prod_ne_zero_iff.mpr fun j hj => zpow_ne_zero _ (hx j (Finset.mem_insert_of_mem hj))),
      v.ord_zpow, ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]

theorem prod_zpow_ne_zero {ι : Type*} (S : Finset ι) (x : ι → F) (n : ι → ℤ) (hx : ∀ i ∈ S, x i ≠ 0) :
    (∏ i ∈ S, x i ^ n i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j hj => zpow_ne_zero _ (hx j hj)

end PlaceLemmas

section ResLemmas
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar] (R : RegularProlongation A F Fbar)

theorem res_ne_zero_of_ord_ne_zero {x : F} (hx : x ∈ R.integers) (w : Place (ResidueField ↥A) Fbar)
    (h : w.ord (R.residue ⟨x, hx⟩) ≠ 0) : R.residue ⟨x, hx⟩ ≠ 0 := by
  intro h0; rw [h0, Place.ord_zero] at h; exact h rfl

theorem ne_zero_of_res_ne_zero {x : F} (hx : x ∈ R.integers) (h : R.residue ⟨x, hx⟩ ≠ 0) : x ≠ 0 := by
  rintro rfl; apply h
  have : (⟨(0 : F), hx⟩ : R.integers) = 0 := rfl
  rw [this, map_zero]

theorem res_inv {x : F} (hx : x ∈ R.integers) (h0 : R.residue ⟨x, hx⟩ ≠ 0) :
    ∃ h' : x⁻¹ ∈ R.integers, R.residue ⟨x⁻¹, h'⟩ = (R.residue ⟨x, hx⟩)⁻¹ := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero h0
  have hcoe : ((u : R.integers) : F) = x := by rw [hu]
  have hinv : (((u⁻¹ : (↥R.integers)ˣ) : R.integers) : F) = x⁻¹ := by
    have h1 : x * (((u⁻¹ : (↥R.integers)ˣ) : R.integers) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hmem : x⁻¹ ∈ R.integers := hinv ▸ SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hx' : (⟨x⁻¹, hmem⟩ : R.integers) = ((u⁻¹ : (↥R.integers)ˣ) : R.integers) := Subtype.ext hinv.symm
  rw [hx', map_units_inv, hu]

theorem res_mul {x y : F} (hx : x ∈ R.integers) (hy : y ∈ R.integers) :
    ∃ h : x * y ∈ R.integers, R.residue ⟨x * y, h⟩ = R.residue ⟨x, hx⟩ * R.residue ⟨y, hy⟩ :=
  ⟨mul_mem hx hy, by rw [← map_mul]; rfl⟩

theorem res_sub {x y : F} (hx : x ∈ R.integers) (hy : y ∈ R.integers) :
    ∃ h : x - y ∈ R.integers, R.residue ⟨x - y, h⟩ = R.residue ⟨x, hx⟩ - R.residue ⟨y, hy⟩ :=
  ⟨sub_mem hx hy, by rw [← map_sub]; rfl⟩

theorem res_pow {x : F} (hx : x ∈ R.integers) (n : ℕ) :
    ∃ h : x ^ n ∈ R.integers, R.residue ⟨x ^ n, h⟩ = (R.residue ⟨x, hx⟩) ^ n :=
  ⟨pow_mem hx n, by rw [← map_pow]; rfl⟩

theorem res_zpow {x : F} (hx : x ∈ R.integers) (h0 : R.residue ⟨x, hx⟩ ≠ 0) (n : ℤ) :
    ∃ h : x ^ n ∈ R.integers, R.residue ⟨x ^ n, h⟩ = (R.residue ⟨x, hx⟩) ^ n := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact res_pow R hx n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    obtain ⟨hp, hrp⟩ := res_pow R hx (n + 1)
    have h0' : R.residue ⟨x ^ (n + 1), hp⟩ ≠ 0 := by rw [hrp]; exact pow_ne_zero _ h0
    obtain ⟨hi, hri⟩ := res_inv R hp h0'
    exact ⟨hi, by rw [hri, hrp]⟩

theorem res_prod_zpow {ι : Type*} (S : Finset ι) (x : ι → F) (r : ι → Fbar) (n : ι → ℤ)
    (hx : ∀ i ∈ S, ∃ h : x i ∈ R.integers, R.residue ⟨x i, h⟩ = r i) (hr : ∀ i ∈ S, r i ≠ 0) :
    ∃ h : (∏ i ∈ S, x i ^ n i) ∈ R.integers, R.residue ⟨∏ i ∈ S, x i ^ n i, h⟩ = ∏ i ∈ S, r i ^ n i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.prod_empty]; exact one_mem _, ?_⟩
    have e : (⟨∏ i ∈ (∅ : Finset ι), x i ^ n i, by rw [Finset.prod_empty]; exact one_mem _⟩ : R.integers) = 1 :=
      Subtype.ext (show (∏ i ∈ (∅ : Finset ι), x i ^ n i) = ((1 : R.integers) : F) by rw [Finset.prod_empty]; rfl)
    rw [e, map_one, Finset.prod_empty]
  | insert i S hi ih =>
    obtain ⟨hmem, hres⟩ := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)) (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    obtain ⟨hxi, hri⟩ := hx i (Finset.mem_insert_self _ _)
    have h0i : R.residue ⟨x i, hxi⟩ ≠ 0 := by rw [hri]; exact hr i (Finset.mem_insert_self _ _)
    obtain ⟨hzi, hrzi⟩ := res_zpow R hxi h0i (n i)
    obtain ⟨hm, hrm⟩ := res_mul R hzi hmem
    refine ⟨by rw [Finset.prod_insert hi]; exact hm, ?_⟩
    have e : (⟨∏ j ∈ insert i S, x j ^ n j, by rw [Finset.prod_insert hi]; exact hm⟩ : R.integers) =
        ⟨x i ^ n i * ∏ j ∈ S, x j ^ n j, hm⟩ := Subtype.ext (Finset.prod_insert hi)
    rw [e, hrm, hrzi, hres, hri, Finset.prod_insert hi]

theorem res_algebraMap (a : ↥A) :
    ∃ h : algebraMap L F (a : L) ∈ R.integers,
      R.residue ⟨algebraMap L F (a : L), h⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) :=
  ⟨(R.algebraMap_mem_iff a).mpr a.2, R.residue_algebraMap a⟩

theorem res_algebraMap_eq_zero (a : ↥A) (ha : a ∈ maximalIdeal ↥A) :
    ∃ h : algebraMap L F (a : L) ∈ R.integers, R.residue ⟨algebraMap L F (a : L), h⟩ = 0 := by
  obtain ⟨h, hr⟩ := res_algebraMap R a
  exact ⟨h, by rw [hr, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]⟩

theorem res_congr {x y : F} (e : x = y) (hx : x ∈ R.integers) (r : Fbar) (hr : R.residue ⟨x, hx⟩ = r) :
    ∃ h : y ∈ R.integers, R.residue ⟨y, h⟩ = r := by
  subst e; exact ⟨hx, hr⟩

end ResLemmas

section Constants
variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem val_coe_unit_eq_one {w : ↥A} (hw : IsUnit w) : A.valuation (w : L) = 1 := by
  obtain ⟨w', rfl⟩ := hw; exact A.valuation_unit w'

theorem mem_of_val_eq_one {x : L} (hx : A.valuation x = 1) : x ∈ A := (A.valuation_le_one_iff x).mp hx.le

theorem residue_ne_zero_of_val_eq_one {x : L} (hx : A.valuation x = 1) :
    IsLocalRing.residue ↥A ⟨x, mem_of_val_eq_one hx⟩ ≠ 0 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]; exact hx

theorem unit_zpow_mem_and_residue (w : ↥A) (hw : IsUnit w) (n : ℤ) :
    ∃ h : (w : L) ^ n ∈ A, IsLocalRing.residue ↥A ⟨(w : L) ^ n, h⟩ = (IsLocalRing.residue ↥A w) ^ n := by
  obtain ⟨wu, hwu⟩ := hw
  have hL : (((wu ^ n : (↥A)ˣ) : ↥A) : L) = (w : L) ^ n := by
    have h := congrArg Units.val (map_zpow (Units.map ((algebraMap (↥A) L : ↥A →+* L) : ↥A →* L)) wu n)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map, MonoidHom.coe_coe, hwu] at h
    exact h
  have hmem : (w : L) ^ n ∈ A := hL ▸ ((wu ^ n : (↥A)ˣ) : ↥A).2
  refine ⟨hmem, ?_⟩
  have e : (⟨(w : L) ^ n, hmem⟩ : ↥A) = ((wu ^ n : (↥A)ˣ) : ↥A) := Subtype.ext hL.symm
  rw [e]
  have h := congrArg Units.val (map_zpow (Units.map ((IsLocalRing.residue ↥A : ↥A →+* ResidueField ↥A) : ↥A →* ResidueField ↥A)) wu n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map, MonoidHom.coe_coe, hwu] at h
  exact h

theorem red_eq_of_eq_zpow_mul (ϖ' : ↥A) (hϖm : ϖ' ∈ IsLocalRing.maximalIdeal ↥A) (hϖ0 : (ϖ' : L) ≠ 0)
    (u : ↥A) (hu : IsLocalRing.residue ↥A u ≠ 0) (X : ↥A) (hX : IsLocalRing.residue ↥A X ≠ 0) (t : ℤ)
    (h : (X : L) = (ϖ' : L) ^ t * (u : L)) : t = 0 ∧ IsLocalRing.residue ↥A X = IsLocalRing.residue ↥A u := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exfalso
    apply hu
    have h1 : (u : L) = (ϖ' : L) ^ (-t).toNat * (X : L) := by
      rw [h, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, one_mul]
    have hu' : u = ϖ' ^ (-t).toNat * X := Subtype.ext (by push_cast; exact h1)
    rw [IsLocalRing.residue_eq_zero_iff, hu']
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))
  · refine ⟨rfl, ?_⟩
    congr 1
    exact Subtype.ext (by rw [h, zpow_zero, one_mul])
  · exfalso
    apply hX
    have hX' : X = ϖ' ^ t.toNat * u := Subtype.ext (by push_cast; rw [h, ← zpow_natCast, Int.toNat_of_nonneg ht.le])
    rw [IsLocalRing.residue_eq_zero_iff, hX']
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))

theorem zpow_val_eq_one_iff {x : L} (hx0 : x ≠ 0) (hx1 : A.valuation x < 1) (k : ℤ) :
    A.valuation x ^ k = 1 ↔ k = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zpow_zero]⟩
  have hpos : 0 < A.valuation x := (Valuation.pos_iff _).mpr hx0
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exfalso
    have h1 : A.valuation x ^ (-k) < 1 := zpow_lt_one₀ hpos hx1 (by omega)
    rw [zpow_neg, h, inv_one] at h1
    exact lt_irrefl _ h1
  · exact hk
  · exact absurd h (zpow_lt_one₀ hpos hx1 hk).ne
end Constants

section ValArith
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem eq_one_of_pow_eq_one' {x : Γ} {N : ℕ} (hN : N ≠ 0) (h : x ^ N = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hl | he | hg
  · exact absurd h (pow_lt_one₀ zero_le' hl hN).ne
  · exact he
  · exact absurd h (one_lt_pow₀ hg hN).ne'

theorem prod_zpow_eq_zpow_sum' {G₀ : Type*} [CommGroupWithZero G₀] {ι : Type*} {a : G₀} (ha : a ≠ 0) (s : Finset ι) (g : ι → ℤ) :
    ∏ i ∈ s, a ^ g i = a ^ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

theorem prod_zpow_neg_mul_zpow_eq_one {ι : Type*} (S : Finset ι) (g : ι → Γ) (P : Γ) (hP : P ≠ 0)
    (d : ι → ℤ) (q : ι → ℚ) (hq : ∀ i ∈ S, 0 < q i)
    (hg : ∀ i ∈ S, g i ^ (q i).den = P ^ (q i).num.toNat)
    (μ : ℤ) (hμ : (∑ i ∈ S, (d i : ℚ) * q i) = μ) :
    (∏ i ∈ S, g i ^ (-(d i))) * P ^ μ = 1 := by
  classical
  set N : ℕ := ∏ i ∈ S, (q i).den with hN
  have hNpos : 0 < N := Finset.prod_pos fun i _ => Rat.den_pos (q i)
  have hdvd : ∀ i ∈ S, (q i).den ∣ N := fun i hi => Finset.dvd_prod_of_mem _ hi

  have hcof : ∀ i ∈ S, ((q i).den : ℤ) * ((N / (q i).den : ℕ) : ℤ) = N := by
    intro i hi
    obtain ⟨c, hc⟩ := hdvd i hi
    rw [hc, Nat.mul_div_cancel_left _ (Rat.den_pos (q i))]; push_cast; ring
  have h1 : ∀ i ∈ S, (g i ^ (-(d i))) ^ N = P ^ (-(d i) * ((q i).num * ((N / (q i).den : ℕ) : ℤ))) := by
    intro i hi
    have hnum : ((q i).num.toNat : ℤ) = (q i).num := Int.toNat_of_nonneg (Rat.num_pos.mpr (hq i hi)).le
    calc (g i ^ (-(d i))) ^ N = (g i ^ ((q i).den : ℤ)) ^ (-(d i) * ((N / (q i).den : ℕ) : ℤ)) := by
            rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← hcof i hi]; congr 1; ring
      _ = (P ^ ((q i).num : ℤ)) ^ (-(d i) * ((N / (q i).den : ℕ) : ℤ)) := by
            rw [zpow_natCast, hg i hi, ← zpow_natCast P, hnum]
      _ = P ^ (-(d i) * ((q i).num * ((N / (q i).den : ℕ) : ℤ))) := by rw [← zpow_mul]; congr 1; ring
  have h2 : (∑ i ∈ S, (-(d i) * ((q i).num * ((N / (q i).den : ℕ) : ℤ)))) + μ * N = 0 := by
    have hq' : ∀ i ∈ S, ((q i).num : ℚ) * ((N / (q i).den : ℕ) : ℚ) = q i * N := by
      intro i hi
      have h := hcof i hi
      have h' : ((q i).den : ℚ) * ((N / (q i).den : ℕ) : ℚ) = N := by exact_mod_cast h
      rw [← h', ← mul_assoc, Rat.mul_den_eq_num]
    have h2q : (((∑ i ∈ S, (-(d i) * ((q i).num * ((N / (q i).den : ℕ) : ℤ)))) + μ * N : ℤ) : ℚ) = 0 := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast]
      rw [Finset.sum_congr rfl (fun i hi => by rw [hq' i hi]), ← hμ, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero (fun i _ => by ring)
    exact Int.cast_injective (α := ℚ) (h2q.trans Int.cast_zero.symm)
  apply eq_one_of_pow_eq_one' hNpos.ne'
  rw [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl h1, prod_zpow_eq_zpow_sum' hP, ← zpow_natCast (P ^ μ), ← zpow_mul,
    ← zpow_add₀ hP, h2, zpow_zero]

end ValArith

section Constants2
variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem res_invA {x : L} (hx : x ∈ A) (h0 : IsLocalRing.residue ↥A ⟨x, hx⟩ ≠ 0) :
    ∃ h : x⁻¹ ∈ A, IsLocalRing.residue ↥A ⟨x⁻¹, h⟩ = (IsLocalRing.residue ↥A ⟨x, hx⟩)⁻¹ := by
  have hxu : IsUnit (⟨x, hx⟩ : ↥A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h0
  obtain ⟨h, hr⟩ := unit_zpow_mem_and_residue ⟨x, hx⟩ hxu (-1)
  have hmem : x⁻¹ ∈ A := by rw [← zpow_neg_one]; exact h
  refine ⟨hmem, ?_⟩
  have e : (⟨x⁻¹, hmem⟩ : ↥A) = ⟨((⟨x, hx⟩ : ↥A) : L) ^ (-1 : ℤ), h⟩ := Subtype.ext (zpow_neg_one x).symm
  rw [e, hr, zpow_neg_one]

theorem zpow_bookkeeping (L : Type*) [Field L] (Pp u Pa s : L) (hP : Pp ≠ 0) (hu : u ≠ 0) (n μ o₁ o₂ t : ℤ) (e : ℕ)
    (ht : t = (e : ℤ) * o₂ - n - μ) :
    Pp ^ t * (s * u ^ o₂ * (Pa * (Pp ^ e * u) ^ (-(o₁ + o₂)) * Pp ^ μ)) = Pp ^ (-n) * (s * Pa) * (Pp ^ e * u) ^ (-o₁) := by
  have hπ : Pp ^ e * u ≠ 0 := mul_ne_zero (pow_ne_zero _ hP) hu
  have h1 : u ^ o₂ * (Pp ^ e * u) ^ (-o₂) = Pp ^ (-((e : ℤ) * o₂)) := by
    rw [mul_zpow, ← zpow_natCast, ← zpow_mul, zpow_neg u, show (e : ℤ) * -o₂ = -((e : ℤ) * o₂) by ring,
      mul_left_comm, mul_inv_cancel₀ (zpow_ne_zero _ hu), mul_one]
  calc Pp ^ t * (s * u ^ o₂ * (Pa * (Pp ^ e * u) ^ (-(o₁ + o₂)) * Pp ^ μ))
      = Pp ^ t * Pp ^ μ * s * Pa * (Pp ^ e * u) ^ (-o₁) * (u ^ o₂ * (Pp ^ e * u) ^ (-o₂)) := by
        rw [neg_add, zpow_add₀ hπ]; ring
    _ = Pp ^ t * Pp ^ μ * Pp ^ (-((e : ℤ) * o₂)) * (s * Pa) * (Pp ^ e * u) ^ (-o₁) := by rw [h1]; ring
    _ = Pp ^ (-n) * (s * Pa) * (Pp ^ e * u) ^ (-o₁) := by
        rw [← zpow_add₀ hP, ← zpow_add₀ hP, show t + μ + -((e : ℤ) * o₂) = -n by omega]

theorem two_radii (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (x : ↥A) (e : ℕ) (he : 0 < e) (u : ↥A) (hu : IsUnit u) (hx : x = ((p : ℕ) : ↥A) ^ e * u) :
    ∃ c₁ c₂ : ↥A, (c₁ ∈ maximalIdeal ↥A ∧ (c₁ : AlgebraicClosure ℚ) ≠ 0 ∧ ∃ m ∈ maximalIdeal ↥A, (x : AlgebraicClosure ℚ) = c₁ * m) ∧
      (c₂ ∈ maximalIdeal ↥A ∧ (c₂ : AlgebraicClosure ℚ) ≠ 0 ∧ ∃ m ∈ maximalIdeal ↥A, (x : AlgebraicClosure ℚ) = c₂ * m) ∧
      A.valuation (c₁ : AlgebraicClosure ℚ) ≠ A.valuation (c₂ : AlgebraicClosure ℚ) := by
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hvp1 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hvp0 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp0
  have hvu : A.valuation ((u : ↥A) : AlgebraicClosure ℚ) = 1 := by obtain ⟨u', rfl⟩ := hu; exact A.valuation_unit u'

  obtain ⟨r₂, hr₂⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℕ) : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  obtain ⟨r₃, hr₃⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℕ) : AlgebraicClosure ℚ) (n := 3) (by norm_num)
  have hv₂ : A.valuation r₂ ^ 2 = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) := by rw [← map_pow, hr₂]
  have hv₃ : A.valuation r₃ ^ 3 = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) := by rw [← map_pow, hr₃]
  have hr₂0 : r₂ ≠ 0 := fun h => hp0 (by rw [← hr₂, h]; norm_num)
  have hr₃0 : r₃ ≠ 0 := fun h => hp0 (by rw [← hr₃, h]; norm_num)

  have hlt₂ : A.valuation r₂ < 1 := by
    by_contra h; push Not at h
    have : (1 : _) ≤ A.valuation r₂ ^ 2 := one_le_pow₀ h
    rw [hv₂] at this; exact absurd hvp1 (not_lt.mpr this)
  have hlt₃ : A.valuation r₃ < 1 := by
    by_contra h; push Not at h
    have : (1 : _) ≤ A.valuation r₃ ^ 3 := one_le_pow₀ h
    rw [hv₃] at this; exact absurd hvp1 (not_lt.mpr this)
  have hmem₂ : r₂ ∈ A := (A.valuation_le_one_iff r₂).mp hlt₂.le
  have hmem₃ : r₃ ∈ A := (A.valuation_le_one_iff r₃).mp hlt₃.le
  have hmax₂ : (⟨r₂, hmem₂⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨r₂, hmem₂⟩).mpr hlt₂
  have hmax₃ : (⟨r₃, hmem₃⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨r₃, hmem₃⟩).mpr hlt₃

  have hxL : (x : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) ^ e * (u : AlgebraicClosure ℚ) := by
    rw [hx, Subring.coe_mul, SubmonoidClass.coe_pow]; rfl
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩

  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := (A.valuation_le_one_iff _).mp hvp1.le
  have hm₂mem : r₂ * ((p : ℕ) : AlgebraicClosure ℚ) ^ e' * (u : AlgebraicClosure ℚ) ∈ A :=
    mul_mem (mul_mem hmem₂ (pow_mem hpA e')) u.2
  have hm₃mem : r₃ ^ 2 * ((p : ℕ) : AlgebraicClosure ℚ) ^ e' * (u : AlgebraicClosure ℚ) ∈ A :=
    mul_mem (mul_mem (pow_mem hmem₃ 2) (pow_mem hpA e')) u.2
  have hm₂max : (⟨_, hm₂mem⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [A.valuation_lt_one_iff]
    show A.valuation (r₂ * ((p : ℕ) : AlgebraicClosure ℚ) ^ e' * (u : AlgebraicClosure ℚ)) < 1
    rw [map_mul, map_mul, map_pow, hvu, mul_one]
    exact mul_lt_one_of_lt_of_le hlt₂ (pow_le_one₀ zero_le' hvp1.le)
  have hm₃max : (⟨_, hm₃mem⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [A.valuation_lt_one_iff]
    show A.valuation (r₃ ^ 2 * ((p : ℕ) : AlgebraicClosure ℚ) ^ e' * (u : AlgebraicClosure ℚ)) < 1
    rw [map_mul, map_mul, map_pow, map_pow, hvu, mul_one]
    exact mul_lt_one_of_lt_of_le (pow_lt_one₀ zero_le' hlt₃ (by norm_num)) (pow_le_one₀ zero_le' hvp1.le)
  refine ⟨⟨r₂, hmem₂⟩, ⟨r₃, hmem₃⟩, ⟨hmax₂, hr₂0, _, hm₂max, ?_⟩, ⟨hmax₃, hr₃0, _, hm₃max, ?_⟩, ?_⟩
  · show (x : AlgebraicClosure ℚ) = r₂ * (r₂ * ((p : ℕ) : AlgebraicClosure ℚ) ^ e' * (u : AlgebraicClosure ℚ))
    rw [hxL, pow_succ, ← hr₂]; ring
  · show (x : AlgebraicClosure ℚ) = r₃ * (r₃ ^ 2 * ((p : ℕ) : AlgebraicClosure ℚ) ^ e' * (u : AlgebraicClosure ℚ))
    rw [hxL, pow_succ, ← hr₃]; ring
  ·
    intro h
    have h6 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ 3 = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ 2 := by
      calc A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ 3 = (A.valuation r₂ ^ 2) ^ 3 := by rw [hv₂]
        _ = (A.valuation r₃ ^ 3) ^ 2 := by rw [show A.valuation r₂ = A.valuation r₃ from h, ← pow_mul, ← pow_mul]
        _ = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ 2 := by rw [hv₃]
    have := (pow_lt_pow_iff_right_of_lt_one₀ ((Valuation.pos_iff _).mpr hp0) hvp1).mpr (show 2 < 3 by norm_num)
    exact absurd h6 this.ne

end Constants2

section Alg
variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem alg_I2 (c₁ c₂ Λ : L) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hΛ : Λ ≠ 0)
    (f W W' : F) (hW : W = algebraMap L F Λ⁻¹ * W') :
    (algebraMap L F (c₂ * (c₁ * Λ)⁻¹))⁻¹ * (c₂ • f * W) = c₁ • f * W' := by
  rw [hW, Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, map_mul, map_inv₀]
  have h1 : algebraMap L F c₁ ≠ 0 := (map_ne_zero _).mpr hc₁
  have h2 : algebraMap L F c₂ ≠ 0 := (map_ne_zero _).mpr hc₂
  have h3 : algebraMap L F Λ ≠ 0 := (map_ne_zero _).mpr hΛ
  field_simp

theorem alg_I3 (c' π : L) (hc' : c' ≠ 0) (hπ : π ≠ 0) (ga gb z Y : F) (hY : Y ≠ 0)
    (hgb : (algebraMap L F c')⁻¹ * ga = gb) (hzY : z = algebraMap L F π * Y⁻¹) (o : ℤ) :
    ga * z ^ o = algebraMap L F (c' * π ^ o) * gb * Y ^ (-o) := by
  rw [← hgb, hzY, mul_zpow, inv_zpow', map_mul, map_zpow₀]
  have h1 : algebraMap L F c' ≠ 0 := (map_ne_zero _).mpr hc'
  have h2 : algebraMap L F π ^ o ≠ 0 := zpow_ne_zero _ ((map_ne_zero _).mpr hπ)
  have h3 : Y ^ o ≠ 0 := zpow_ne_zero _ hY
  rw [zpow_neg]
  field_simp

end Alg

section AnnulusLemmas
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F] (An : Annulus A F)

theorem isRational_of_mem {P : Place L F} (hP : P ∈ An.dom) : P.IsRational := (An.mem_dom P hP).1

theorem hasValue_param {P : Place L F} (hP : P ∈ An.dom) : P.HasValue An.param (P.evalAt An.param) := by
  obtain ⟨hrat, hzO, -, -, -⟩ := An.mem_dom P hP
  exact hasValue_evalAt hrat hzO

theorem evalAt_param_mem {P : Place L F} (hP : P ∈ An.dom) : P.evalAt An.param ∈ A := by
  obtain ⟨-, -, ⟨h, -⟩, -, -⟩ := An.mem_dom P hP; exact h

theorem evalAt_param_mem_maximalIdeal {P : Place L F} (hP : P ∈ An.dom) :
    (⟨P.evalAt An.param, evalAt_param_mem An hP⟩ : ↥A) ∈ maximalIdeal ↥A := by
  obtain ⟨-, -, ⟨h, hm⟩, -, -⟩ := An.mem_dom P hP; exact hm

theorem evalAt_param_ne_zero {P : Place L F} (hP : P ∈ An.dom) : P.evalAt An.param ≠ 0 := by
  obtain ⟨-, -, -, h, -⟩ := An.mem_dom P hP; exact h

theorem val_evalAt_param_lt_one {P : Place L F} (hP : P ∈ An.dom) : A.valuation (P.evalAt An.param) < 1 :=
  (A.valuation_lt_one_iff _).mp (evalAt_param_mem_maximalIdeal An hP)

theorem modulus_div_evalAt_mem {P : Place L F} (hP : P ∈ An.dom) :
    ∃ h : (An.modulus : L) * (P.evalAt An.param)⁻¹ ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A := by
  obtain ⟨-, -, -, hz0, m, hm, hπ⟩ := An.mem_dom P hP
  have e : (An.modulus : L) * (P.evalAt An.param)⁻¹ = (m : L) := by
    rw [hπ, mul_comm, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  refine ⟨e ▸ m.2, ?_⟩
  have e' : (⟨_, e ▸ m.2⟩ : ↥A) = m := Subtype.ext e
  rw [e']; exact hm

theorem eq_of_evalAt_param_eq {P V : Place L F} (hP : P ∈ An.dom) (hV : V ∈ An.dom)
    (h : P.evalAt An.param = V.evalAt An.param) : P = V := by
  obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, hm⟩ := An.mem_dom V hV
  obtain ⟨Q, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨_, hzA⟩ hzmax hz0 hm
  exact (huniq P ⟨hP, h⟩).trans (huniq V ⟨hV, rfl⟩).symm

theorem ord_param_sub_evalAt_of_ne {P V : Place L F} (hP : P ∈ An.dom) (hV : V ∈ An.dom) (h : P ≠ V) :
    P.ord (An.param - algebraMap L F (V.evalAt An.param)) = 0 :=
  (hasValue_sub (hasValue_param An hP) (P.hasValue_algebraMap (V.evalAt An.param))).ord_eq_zero
    (sub_ne_zero.mpr fun e => h (eq_of_evalAt_param_eq An hP hV e))

theorem ord_param_eq_zero {P : Place L F} (hP : P ∈ An.dom) : P.ord An.param = 0 :=
  (hasValue_param An hP).ord_eq_zero (evalAt_param_ne_zero An hP)

theorem param_ne_zero (hne : ∃ P, P ∈ An.dom) : An.param ≠ 0 := by
  obtain ⟨P, hP⟩ := hne
  exact (hasValue_param An hP).ne_zero (evalAt_param_ne_zero An hP)

theorem param_sub_ne_zero {V : Place L F} (hV : V ∈ An.dom) : An.param - algebraMap L F (V.evalAt An.param) ≠ 0 := by
  intro h
  have h1 := An.ord_param_sub V hV
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

open Classical in

theorem ord_prod_param_sub (D : Divisor L F) (P : Place L F) (hP : P ∈ An.dom) :
    P.ord (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) = -(D P) := by
  rw [ord_prod_zpow P _ _ _ (fun V hV => param_sub_ne_zero An (Finset.mem_filter.mp hV).2)]
  have h : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom),
      -(D V) * P.ord (An.param - algebraMap L F (V.evalAt An.param)) = if P = V then -(D V) else 0 := by
    intro V hV
    split_ifs with hPV
    · subst hPV; rw [An.ord_param_sub P hP, mul_one]
    · rw [ord_param_sub_evalAt_of_ne An hP (Finset.mem_filter.mp hV).2 hPV, mul_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  split_ifs with hPS
  · rfl
  · rw [Finset.mem_filter, not_and_or] at hPS
    rcases hPS with h1 | h1
    · rw [Finsupp.notMem_support_iff.mp h1, neg_zero]
    · exact absurd hP h1

open Classical in

theorem ord_mul_prod_eq_zero (f : F) (hf : f ≠ 0) (D : Divisor L F) (hD : ∀ P ∈ An.dom, D P = P.ord f)
    (P : Place L F) (hP : P ∈ An.dom) :
    P.ord (f * ∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) = 0 := by
  rw [P.ord_mul hf (prod_zpow_ne_zero _ _ _ (fun V hV => param_sub_ne_zero An (Finset.mem_filter.mp hV).2)),
    ord_prod_param_sub An D P hP, ← hD P hP, add_neg_cancel]

end AnnulusLemmas

section Core
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]

open Classical in

theorem core (An : Annulus A F)
    (Pp : ↥A) (hPp0 : (Pp : L) ≠ 0) (hPp1 : A.valuation (Pp : L) < 1) (e : ℕ) (u : ↥A) (hu : IsUnit u)
    (hmod : An.modulus = Pp ^ e * u) (u0 : (ResidueField ↥A)ˣ) (hu0 : IsLocalRing.residue ↥A u = u0)
    (Ra : RegularProlongation A F Fbar) (xa : Place (ResidueField ↥A) Fbar)
    (hza : An.param ∈ Ra.integers) (hxa : xa.ord (Ra.residue ⟨An.param, hza⟩) = 1)
    (hslope_a : ∀ (f : F) (hf : f ∈ Ra.integers), Ra.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ra.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (Rb : RegularProlongation A F Fbar) (xb : Place (ResidueField ↥A) Fbar)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    (hnode : ∀ (g : F) (ha : g ∈ Ra.integers) (hb : g ∈ Rb.integers), Ra.residue ⟨g, ha⟩ ≠ 0 → Rb.residue ⟨g, hb⟩ ≠ 0 →
      (∀ V : Place L F, V.ord g ≠ 0 → V ∉ An.dom) →
      ∃ c : ResidueField ↥A, c ≠ 0 ∧ xb.HasValue (Rb.residue ⟨g, hb⟩) c ∧ xa.HasValue (Ra.residue ⟨g, ha⟩) c)
    (q : Place L F → ℚ)
    (hq : ∀ V ∈ An.dom, 0 < q V ∧
      A.valuation (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (q V).den = A.valuation (Pp : L) ^ (q V).num.toNat)
    (f : F) (hf0 : f ≠ 0) (D : Divisor L F) (hD : ∀ P ∈ An.dom, D P = P.ord f)
    (μ : ℤ) (hμ : (∑ V ∈ D.support with V ∈ An.dom, (D V : ℚ) * q V) = μ)
    (c₁ : L) (h₁ : c₁ • f ∈ Rb.integers) (hr₁ : Rb.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (n : ℤ) (h₂ : (c₁ * (Pp : L) ^ n) • f ∈ Ra.integers) (hr₂ : Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩ ≠ 0)
    (hN : (∑ V ∈ D.support with V ∈ An.dom, D V) =
      xb.ord (Rb.residue ⟨c₁ • f, h₁⟩) + xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩)) :
    ∃ (hX : (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (-(D V))) * (Pp : L) ^ μ ∈ A)
      (hX0 : IsLocalRing.residue ↥A ⟨_, hX⟩ ≠ 0),
      ∃ α₁ α₂ : (ResidueField ↥A)ˣ,
        xb.HasValue (Rb.residue ⟨c₁ • f, h₁⟩ / (Rb.residue ⟨_, hzb⟩) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))) (α₁ : ResidueField ↥A) ∧
        xa.HasValue (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩ / (Ra.residue ⟨An.param, hza⟩) ^
          (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩))) (α₂ : ResidueField ↥A) ∧
        α₁ / α₂ = (-1 : (ResidueField ↥A)ˣ) ^ (∑ V ∈ D.support with V ∈ An.dom, D V) *
          u0 ^ (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩)) * Units.mk0 _ hX0 := by

  have hζ0 : Ra.residue ⟨An.param, hza⟩ ≠ 0 := res_ne_zero_of_ord_ne_zero Ra hza xa (by rw [hxa]; exact one_ne_zero)
  have hη0 : Rb.residue ⟨(algebraMap L F (An.modulus : L) * An.param⁻¹), hzb⟩ ≠ 0 := res_ne_zero_of_ord_ne_zero Rb hzb xb (by rw [hxb]; exact one_ne_zero)
  have hz0 : An.param ≠ 0 := ne_zero_of_res_ne_zero Ra hza hζ0
  have hu1 : A.valuation (u : L) = 1 := val_coe_unit_eq_one hu
  have huL0 : (u : L) ≠ 0 := fun h => by rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hπL : (An.modulus : L) = (Pp : L) ^ e * (u : L) := by rw [hmod]; rfl
  have hπ0 : (An.modulus : L) ≠ 0 := by rw [hπL]; exact mul_ne_zero (pow_ne_zero _ hPp0) huL0
  have hy0 : (algebraMap L F (An.modulus : L) * An.param⁻¹) ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hπ0) (inv_ne_zero hz0)
  have hc₁0 : c₁ ≠ 0 := Rb.smul_const_ne_zero h₁ hr₁
  have hc₂0 : (c₁ * (Pp : L) ^ n) ≠ 0 := Ra.smul_const_ne_zero h₂ hr₂
  have hredu0 : IsLocalRing.residue ↥A u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr hu
  have hPpmax : Pp ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff Pp).mpr hPp1
  have haV : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom), V ∈ An.dom := fun V hV => (Finset.mem_filter.mp hV).2
  have ha0 : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom), V.evalAt An.param ≠ 0 := fun V hV => evalAt_param_ne_zero An (haV V hV)

  have hW0 : (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) ≠ 0 := prod_zpow_ne_zero _ _ _ (fun V hV => param_sub_ne_zero An (haV V hV))
  have hGord : ∀ P ∈ An.dom, P.ord (f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V)))) = 0 := ord_mul_prod_eq_zero An f hf0 D hD

  have hfacA : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom), ∃ h : (An.param - algebraMap L F (V.evalAt An.param)) ∈ Ra.integers,
      Ra.residue ⟨_, h⟩ = Ra.residue ⟨An.param, hza⟩ := by
    intro V hV
    obtain ⟨hc, hrc⟩ := res_algebraMap_eq_zero Ra ⟨V.evalAt An.param, evalAt_param_mem An (haV V hV)⟩ (evalAt_param_mem_maximalIdeal An (haV V hV))
    obtain ⟨hs, hrs⟩ := res_sub Ra hza hc
    exact ⟨hs, by rw [hrs, hrc, sub_zero]⟩
  obtain ⟨hWa, hrWa⟩ := res_prod_zpow Ra (D.support.filter (fun V => V ∈ An.dom)) _ (fun _ => Ra.residue ⟨An.param, hza⟩) (fun V => -(D V)) hfacA (fun _ _ => hζ0)
  have hrWa' : Ra.residue ⟨(∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))), hWa⟩ = (Ra.residue ⟨An.param, hza⟩) ^ (-(∑ V ∈ D.support with V ∈ An.dom, D V)) := by
    rw [hrWa, prod_zpow_eq_zpow_sum' hζ0, Finset.sum_neg_distrib]
  obtain ⟨hga, hrga⟩ := res_mul Ra h₂ hWa
  have hrga0 : Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))), hga⟩ ≠ 0 := by
    rw [hrga, hrWa']; exact mul_ne_zero hr₂ (zpow_ne_zero _ hζ0)
  have hga_ne : (c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) ≠ 0 := ne_zero_of_res_ne_zero Ra hga hrga0
  have hga_ord : ∀ P ∈ An.dom, P.ord ((c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V)))) = 0 := by
    intro P hP
    rw [smul_mul_assoc, Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc₂0) (mul_ne_zero hf0 hW0), ord_algebraMap', hGord P hP, add_zero]

  have hfacB : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom),
      ∃ h : (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) ∈ Rb.integers, Rb.residue ⟨_, h⟩ = 1 := by
    intro V hV
    obtain ⟨hmA, hmmax⟩ := modulus_div_evalAt_mem An (haV V hV)
    obtain ⟨hc, hrc⟩ := res_algebraMap_eq_zero Rb ⟨_, hmA⟩ hmmax
    obtain ⟨hi, hri⟩ := res_inv Rb hzb hη0
    obtain ⟨hm, hrm⟩ := res_mul Rb hc hi
    obtain ⟨hs, hrs⟩ := res_sub Rb (one_mem _) hm
    refine ⟨hs, ?_⟩
    rw [hrs, hrm, hrc, zero_mul, sub_zero]; exact map_one Rb.residue
  obtain ⟨hWb, hrWb⟩ := res_prod_zpow Rb (D.support.filter (fun V => V ∈ An.dom)) _ (fun _ => (1 : Fbar)) (fun V => -(D V)) hfacB (fun _ _ => one_ne_zero)
  have hrWb' : Rb.residue ⟨(∏ V ∈ D.support with V ∈ An.dom, (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) ^ (-(D V))), hWb⟩ = 1 := by rw [hrWb]; simp
  obtain ⟨hgb, hrgb⟩ := res_mul Rb h₁ hWb
  have hrgb' : Rb.residue ⟨c₁ • f * (∏ V ∈ D.support with V ∈ An.dom, (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) ^ (-(D V))), hgb⟩ = Rb.residue ⟨c₁ • f, h₁⟩ := by rw [hrgb, hrWb', mul_one]

  have hΛ0 : (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)) ≠ 0 := prod_zpow_ne_zero _ _ _ (fun V hV => neg_ne_zero.mpr (ha0 V hV))
  have hfid : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom),
      An.param - algebraMap L F (V.evalAt An.param) =
        algebraMap L F (-(V.evalAt An.param)) * (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) := by
    intro V hV
    have ha := ha0 V hV
    have hCa : algebraMap L F (V.evalAt An.param) ≠ 0 := (map_ne_zero _).mpr ha
    have hCπ : algebraMap L F (An.modulus : L) ≠ 0 := (map_ne_zero _).mpr hπ0
    rw [map_neg, map_mul, map_inv₀]
    field_simp
    ring
  have hWfac : (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) = algebraMap L F ((∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹ * (∏ V ∈ D.support with V ∈ An.dom, (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) ^ (-(D V))) := by
    rw [Finset.prod_congr rfl (fun V hV => by rw [hfid V hV, mul_zpow]), Finset.prod_mul_distrib, map_inv₀, map_prod, ← Finset.prod_inv_distrib]
    congr 1
    exact Finset.prod_congr rfl (fun V _ => by rw [zpow_neg, map_zpow₀])

  have hc'0 : (c₁ * (Pp : L) ^ n) * (c₁ * (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹ ≠ 0 := mul_ne_zero hc₂0 (inv_ne_zero (mul_ne_zero hc₁0 hΛ0))
  have hI2 := alg_I2 c₁ (c₁ * (Pp : L) ^ n) (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)) hc₁0 hc₂0 hΛ0 f (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) (∏ V ∈ D.support with V ∈ An.dom, (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) ^ (-(D V))) hWfac
  obtain ⟨hgb2, hrgb2⟩ := res_congr Rb hI2.symm hgb _ hrgb'
  have hrgb20 : Rb.residue ⟨_, hgb2⟩ ≠ 0 := by rw [hrgb2]; exact hr₁

  obtain ⟨-, hprod⟩ := Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation An hπ0
    Ra xa hza hxa hslope_a Rb xb hzb hxb hslope_b hwide ((c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V)))) hga_ne hga hrga0
    ((c₁ * (Pp : L) ^ n) * (c₁ * (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹) hc'0 hgb2 hrgb20 0 (fun P hP => absurd hP (by simp))
    (fun P hP => by rw [Finsupp.coe_zero, Pi.zero_apply, hga_ord P hP])
  rw [Finsupp.prod_zero_index, hrgb2] at hprod

  have hω1 : A.valuation ((c₁ * (Pp : L) ^ n) * (c₁ * (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹ * (An.modulus : L) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))) = 1 := by
    rw [map_mul, map_zpow₀]; exact hprod.symm
  have hωA : (c₁ * (Pp : L) ^ n) * (c₁ * (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹ * (An.modulus : L) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩)) ∈ A := mem_of_val_eq_one hω1
  have hωred : IsLocalRing.residue ↥A ⟨_, hωA⟩ ≠ 0 := residue_ne_zero_of_val_eq_one hω1

  obtain ⟨hzo, hrzo⟩ := res_zpow Ra hza hζ0 (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))
  obtain ⟨hUa, hrUa⟩ := res_mul Ra hga hzo
  have hrUa' : Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) * An.param ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩)), hUa⟩ =
      Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩ / (Ra.residue ⟨An.param, hza⟩) ^ (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩)) := by
    rw [hrUa, hrga, hrWa', hrzo, mul_assoc, ← zpow_add₀ hζ0, div_eq_mul_inv, ← zpow_neg]
    congr 2
    linarith [hN]
  have hrUa0 : Ra.residue ⟨_, hUa⟩ ≠ 0 := by rw [hrUa']; exact div_ne_zero hr₂ (zpow_ne_zero _ hζ0)

  have hzπy : An.param = algebraMap L F (An.modulus : L) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel₀ ((map_ne_zero _).mpr hπ0), mul_one]
  have hI3 := alg_I3 ((c₁ * (Pp : L) ^ n) * (c₁ * (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹) (An.modulus : L) hc'0 hπ0 ((c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V)))) (c₁ • f * (∏ V ∈ D.support with V ∈ An.dom, (1 - algebraMap L F ((An.modulus : L) * (V.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹) ^ (-(D V)))) An.param (algebraMap L F (An.modulus : L) * An.param⁻¹) hy0 hI2 hzπy
    (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))
  obtain ⟨hωb, hrωb⟩ := res_algebraMap Rb ⟨_, hωA⟩
  obtain ⟨hyo, hryo⟩ := res_zpow Rb hzb hη0 (-(xb.ord (Rb.residue ⟨c₁ • f, h₁⟩)))
  obtain ⟨hm1, hrm1⟩ := res_mul Rb hωb hgb
  obtain ⟨hm2, hrm2⟩ := res_mul Rb hm1 hyo
  obtain ⟨hUb, hrUb⟩ := res_congr Rb hI3.symm hm2 _ hrm2
  have hrUb' : Rb.residue ⟨(c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) * An.param ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩)), hUb⟩ =
      algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A ⟨_, hωA⟩) * (Rb.residue ⟨c₁ • f, h₁⟩ / (Rb.residue ⟨(algebraMap L F (An.modulus : L) * An.param⁻¹), hzb⟩) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))) := by
    rw [hrUb, hrm1, hrωb, hrgb', hryo, div_eq_mul_inv, ← zpow_neg, mul_assoc]
  have hCω0 : algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A ⟨_, hωA⟩) ≠ 0 := (map_ne_zero _).mpr hωred
  have hrUb0 : Rb.residue ⟨_, hUb⟩ ≠ 0 := by
    rw [hrUb']; exact mul_ne_zero hCω0 (div_ne_zero hr₁ (zpow_ne_zero _ hη0))

  have hUord : ∀ V : Place L F, V.ord ((c₁ * (Pp : L) ^ n) • f * (∏ V ∈ D.support with V ∈ An.dom, (An.param - algebraMap L F (V.evalAt An.param)) ^ (-(D V))) * An.param ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))) ≠ 0 → V ∉ An.dom := by
    intro V hV hVd
    apply hV
    rw [V.ord_mul hga_ne (zpow_ne_zero _ hz0), hga_ord V hVd, V.ord_zpow, ord_param_eq_zero An hVd, mul_zero, add_zero]

  obtain ⟨c, hc0, hvb, hva⟩ := hnode _ hUa hUb hrUa0 hrUb0 hUord
  rw [hrUa'] at hva
  rw [hrUb'] at hvb
  have hvb' : xb.HasValue (Rb.residue ⟨c₁ • f, h₁⟩ / (Rb.residue ⟨(algebraMap L F (An.modulus : L) * An.param⁻¹), hzb⟩) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩))) ((IsLocalRing.residue ↥A ⟨_, hωA⟩)⁻¹ * c) := by
    have h := (xb.hasValue_algebraMap ((IsLocalRing.residue ↥A ⟨_, hωA⟩)⁻¹)).mul hvb
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hωred, map_one, one_mul] at h

  have hbV : ∀ V ∈ D.support.filter (fun V => V ∈ An.dom), V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹) = (An.modulus : L) * (V.evalAt An.param)⁻¹ := by
    intro V hV
    exact evalAt_eq_of_hasValue (isRational_of_mem An (haV V hV))
      ((V.hasValue_algebraMap (An.modulus : L)).mul ((hasValue_param An (haV V hV)).inv (ha0 V hV)))
  have hX1 : A.valuation ((∏ V ∈ D.support with V ∈ An.dom, (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (-(D V))) * (Pp : L) ^ μ) = 1 := by
    rw [map_mul, map_prod, map_zpow₀]
    simp only [map_zpow₀]
    exact prod_zpow_neg_mul_zpow_eq_one _ (fun V => A.valuation (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹))) _ ((Valuation.ne_zero_iff _).mpr hPp0)
      (fun V => D V) q (fun V hV => (hq V (haV V hV)).1) (fun V hV => (hq V (haV V hV)).2) μ hμ
  have hXA : ((∏ V ∈ D.support with V ∈ An.dom, (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (-(D V))) * (Pp : L) ^ μ) ∈ A := mem_of_val_eq_one hX1
  have hXred : IsLocalRing.residue ↥A ⟨_, hXA⟩ ≠ 0 := residue_ne_zero_of_val_eq_one hX1

  have hPa0 : (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt An.param) ^ (D V)) ≠ 0 := prod_zpow_ne_zero _ _ _ ha0
  have hXeq : ((∏ V ∈ D.support with V ∈ An.dom, (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (-(D V))) * (Pp : L) ^ μ) = (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt An.param) ^ (D V)) * (An.modulus : L) ^ (-(∑ V ∈ D.support with V ∈ An.dom, D V)) * (Pp : L) ^ μ := by
    rw [Finset.prod_congr rfl (fun V hV => by rw [hbV V hV, mul_zpow, inv_zpow', neg_neg]), Finset.prod_mul_distrib,
      prod_zpow_eq_zpow_sum' hπ0, Finset.sum_neg_distrib]
    ring
  have hΛeq : (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)) = (-1 : L) ^ (∑ V ∈ D.support with V ∈ An.dom, D V) * (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt An.param) ^ (D V)) := by
    rw [Finset.prod_congr rfl (fun V _ => by rw [neg_eq_neg_one_mul, mul_zpow]), Finset.prod_mul_distrib,
      prod_zpow_eq_zpow_sum' (neg_ne_zero.mpr one_ne_zero)]

  obtain ⟨hsA, hrs⟩ := unit_zpow_mem_and_residue (-1 : ↥A) isUnit_one.neg (∑ V ∈ D.support with V ∈ An.dom, D V)
  obtain ⟨huA, hru⟩ := unit_zpow_mem_and_residue u hu (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩))
  have hEA : ((-1 : ↥A) : L) ^ (∑ V ∈ D.support with V ∈ An.dom, D V) * (u : L) ^ (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩)) * ((∏ V ∈ D.support with V ∈ An.dom, (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (-(D V))) * (Pp : L) ^ μ) ∈ A := mul_mem (mul_mem hsA huA) hXA
  have hEred : IsLocalRing.residue ↥A ⟨_, hEA⟩ =
      (IsLocalRing.residue ↥A (-1)) ^ (∑ V ∈ D.support with V ∈ An.dom, D V) * (IsLocalRing.residue ↥A u) ^ (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩)) * IsLocalRing.residue ↥A ⟨_, hXA⟩ := by
    have e3 : (⟨_, hEA⟩ : ↥A) = ⟨_, hsA⟩ * ⟨_, huA⟩ * ⟨_, hXA⟩ := rfl
    rw [e3, map_mul, map_mul, hrs, hru]
  have hEred0 : IsLocalRing.residue ↥A ⟨_, hEA⟩ ≠ 0 := by
    rw [hEred, map_neg, map_one]
    exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (zpow_ne_zero _ hredu0)) hXred
  obtain ⟨hωiA, hrωi⟩ := res_invA hωA hωred
  have hexp : ((⟨_, hωiA⟩ : ↥A) : L) = (Pp : L) ^ ((e : ℤ) * xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩) - n - μ) * ((⟨_, hEA⟩ : ↥A) : L) := by
    show ((c₁ * (Pp : L) ^ n) * (c₁ * (∏ V ∈ D.support with V ∈ An.dom, (-(V.evalAt An.param)) ^ (D V)))⁻¹ * (An.modulus : L) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩)))⁻¹ =
      (Pp : L) ^ ((e : ℤ) * xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩) - n - μ) * (((-1 : ↥A) : L) ^ (∑ V ∈ D.support with V ∈ An.dom, D V) * (u : L) ^ (xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩)) * ((∏ V ∈ D.support with V ∈ An.dom, (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (-(D V))) * (Pp : L) ^ μ))
    rw [hXeq, hΛeq, hπL, hN]
    push_cast
    rw [zpow_bookkeeping L (Pp : L) (u : L) (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt An.param) ^ (D V)) ((-1 : L) ^ (xb.ord (Rb.residue ⟨c₁ • f, h₁⟩) + xa.ord (Ra.residue ⟨(c₁ * (Pp : L) ^ n) • f, h₂⟩))) hPp0 huL0 n μ _ _ _ e rfl]
    have hQ0 : ((Pp : L) ^ e * (u : L)) ≠ 0 := mul_ne_zero (pow_ne_zero _ hPp0) huL0
    first
      | (field_simp
         rw [← zpow_add₀ hPp0, add_neg_cancel, zpow_zero, one_mul, zpow_neg, one_div])
      | (simp only [zpow_neg]; field_simp; done)
      | (simp only [zpow_neg]; field_simp; ring)
  obtain ⟨ht0, hredω⟩ := red_eq_of_eq_zpow_mul Pp hPpmax hPp0 ⟨_, hEA⟩ hEred0 ⟨_, hωiA⟩ (by rw [hrωi]; exact inv_ne_zero hωred) _ hexp

  refine ⟨hXA, hXred, Units.mk0 _ (mul_ne_zero (inv_ne_zero hωred) hc0), Units.mk0 c hc0, hvb', hva, ?_⟩
  ext
  push_cast
  rw [Units.val_mk0, Units.val_mk0, Units.val_mk0, mul_div_assoc, div_self hc0, mul_one, ← hrωi, hredω, hEred, map_neg, map_one, hu0]

end Core

end AngH

open Classical in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hFixRegFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hFixRegSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)

    (dat : JHPlaceSpecialization.TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

    (hunifFst : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 (1 : ℤ) + dat.corrFst s) v = v.ord (dat.unifFst s)) ∧
      (∀ s' ∈ SS, dat.corrFst s s'.1 = 0 ∧ dat.corrFst s s'.2 = 0) ∧ Divisor.degree (dat.corrFst s) = -1)
    (hunifSnd : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 (1 : ℤ) + dat.corrSnd s) v = v.ord (dat.unifSnd s)) ∧
      (∀ s' ∈ SS, dat.corrSnd s s'.1 = 0 ∧ dat.corrSnd s s'.2 = 0) ∧ Divisor.degree (dat.corrSnd s) = -1)

    (hu0 : ∀ s : ↥SS, ∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u ∧ IsLocalRing.residue ↥A u = dat.u0 s)

    (hlam : ∀ (s : ↥SS) (h₁ : JHPlaceSpecialization.flipParam SS An s ∈ Rpd.R₁.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
        ((Rpd.R₁.residue ⟨_, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifFst s) (dat.lam s : ResidueField ↥A))
    (hmu : ∀ (s : ↥SS) (h₂ : (An s).param ∈ Rpd.R₂.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
        ((Rpd.R₂.residue ⟨_, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifSnd s) (dat.mu s : ResidueField ↥A))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (a : JHPlaceSpecialization.TwistVec ↥SS)
    (ha : Psp.IsTwistOf α (θ.toAlgHom.comp α) hα hβ δ SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS)
    (hsp : GluedPic0.mk SS ⟨Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0)

    (s : ↥SS) (f : ↥(xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (Df : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDf : ∀ V, Df V = V.ord f)
    (hDfst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ (An s).dom, Df ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = Df V)
    (hmom : (JHPlaceSpecialization.twistPosMoment SS An pos Df s).den = 1)
    (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (n : ℤ) (h₂ : (c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ n) • f ∈ Rpd.R₂.integers) (hr₂ : Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ n) • f, h₂⟩ ≠ 0)
    (hz₁ : JHPlaceSpecialization.flipParam SS An s ∈ Rpd.R₁.integers) (hz₂ : (An s).param ∈ Rpd.R₂.integers)

    (hN : JHPlaceSpecialization.twistAnnulusDeg SS An Df s =
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ n) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    ∃ α₁ α₂ : (ResidueField ↥A)ˣ,
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
        ((Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / (Rpd.R₁.residue ⟨_, hz₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ^ ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
        (α₁ : ResidueField ↥A) ∧
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
        ((Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ n) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / (Rpd.R₂.residue ⟨_, hz₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ^
          ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ n) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
        (α₂ : ResidueField ↥A) ∧
      α₁ / α₂ =
        (-1 : (ResidueField ↥A)ˣ) ^ (JHPlaceSpecialization.twistAnnulusDeg SS An Df s) *
        dat.u0 s ^ ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ n) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) *
        JHPlaceSpecialization.twistAngFactor SS An pos Df s := by

  obtain ⟨hdom, -, -, -, -, ⟨hz₂', hxa, hslope_a⟩, ⟨hz₁', hxb, hslope_b⟩⟩ := hAn s
  obtain ⟨u, hu, hmod, hu0'⟩ := hu0 s
  have hvp1 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := (A.valuation_le_one_iff _).mp hvp1.le
  have hPp : ((p : ℕ) : ↥A) = ⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ := Subtype.ext (by push_cast; rfl)
  have hmod' : (An s).modulus = (⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ : ↥A) ^ (e s) * u := by rw [← hPp]; exact hmod

  obtain ⟨r₁, r₂, ⟨hr₁m, hr₁0, hr₁d⟩, ⟨hr₂m, hr₂0, hr₂d⟩, hne⟩ := AngH.two_radii A Fact.out hA (An s).modulus (e s) (he s) u hu hmod
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := (An s).existsUnique_evalAt_eq r₁ hr₁m hr₁0 hr₁d
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := (An s).existsUnique_evalAt_eq r₂ hr₂m hr₂0 hr₂d
  have hwide : ∃ Q₁ ∈ (An s).dom, ∃ Q₂ ∈ (An s).dom, A.valuation (Q₁.evalAt (An s).param) ≠ A.valuation (Q₂.evalAt (An s).param) :=
    ⟨Q₁, hQ₁, Q₂, hQ₂, by rw [hQ₁v, hQ₂v]; exact hne⟩

  obtain ⟨hss2, hs1⟩ := (ModularCurve.mem_ssNodePairsQExp_iff s.1).mp ((hSS s.1).mp s.2)
  have hfix2 : JHPlaceSpecialization.Fixed p M H hpM A δ (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 :=
    (hFix _ hss2).1
  have hfix1 : JHPlaceSpecialization.Fixed p M H hpM A δ (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 := by
    rw [hs1]; exact (hFix _ hss2).2
  have hnode : ∀ (g : ↥(xHFunctionFieldBar M H)) (ha : g ∈ Rpd.R₂.integers) (hb : g ∈ Rpd.R₁.integers),
      Rpd.R₂.residue ⟨g, ha⟩ ≠ 0 → Rpd.R₁.residue ⟨g, hb⟩ ≠ 0 →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord g ≠ 0 → V ∉ (An s).dom) →
      ∃ c : (ResidueField ↥A), c ≠ 0 ∧
        (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1.HasValue (Rpd.R₁.residue ⟨g, hb⟩ : Fbar p M H hpM (ResidueField ↥A)) c ∧
        (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2.HasValue (Rpd.R₂.residue ⟨g, ha⟩ : Fbar p M H hpM (ResidueField ↥A)) c := by
    intro g ha hb hra hrb hV
    refine hnv g hb ha hrb hra s.1 s.2 (fun V hVord hread => hV V hVord ((hdom V).mpr ⟨hread.1, ?_, ?_⟩))
    · exact fun hS => hS.2 (by rw [hread.1]; exact hfix1)
    · exact fun hS => hS.2 (by rw [hread.2]; exact hfix2)

  obtain ⟨hX, hX0, α₁, α₂, hv₁, hv₂, heq⟩ := AngH.core (Fbar := Fbar p M H hpM (ResidueField ↥A)) (An s)
    ⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ hp0 hvp1 (e s) u hu hmod' (dat.u0 s) hu0'
    Rpd.R₂ (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 hz₂ hxa hslope_a
    Rpd.R₁ (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 hz₁ hxb hslope_b
    hwide hnode (pos s) (fun V hV => ⟨(hpos s V hV).1, (hpos s V hV).2.2⟩)
    f hf0 Df (fun P _ => hDf P)
    (JHPlaceSpecialization.twistPosMoment SS An pos Df s).num (Rat.coe_int_num_of_den_eq_one hmom).symm
    c₁ h₁ hr₁ n h₂ hr₂ hN

  have hΘ : JHPlaceSpecialization.twistAngFactor SS An pos Df s = Units.mk0 _ hX0 := by
    unfold JHPlaceSpecialization.twistAngFactor
    rw [dif_pos ⟨hmom, hX, hX0⟩]
    exact Units.ext rfl
  refine ⟨α₁, α₂, hv₁, hv₂, ?_⟩
  rw [hΘ]
  exact heq

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_exists_hasValue_residue_div_pow_and_div_eq_twistAngFactor_of_coupled_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_hasValue_residue_div_pow_and_div_eq_twistAngFactor_of_coupled_of_inertiaStable (solution)
