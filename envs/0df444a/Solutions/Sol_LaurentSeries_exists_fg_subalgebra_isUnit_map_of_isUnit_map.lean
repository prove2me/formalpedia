-- Prove2me | solution 1 for LaurentSeries.exists_fg_subalgebra_isUnit_map_of_isUnit_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c995c7ff-06c6-50c0-b91b-8bb4e9dc7902

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_exists_fg_subalgebra_isUnit_map_of_isUnit_map

set_option autoImplicit false

universe u v

noncomputable section

open HahnSeries

namespace LaurentSeries
p2m_export "LaurentSeries" "powerSeriesPart algebraMap_apply ofPowerSeries_powerSeriesPart powerSeriesPart_coeff"
namespace UnitDescent
p2m_open "LaurentSeries"

variable {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]

def CB (B : Subalgebra A R) : Subring (LaurentSeries R) :=
  (ModularCurve.coeffMap (algebraMap B R)).range

theorem mem_CB_iff (B : Subalgebra A R) (y : LaurentSeries R) : y ∈ CB B ↔ ∀ n, y.coeff n ∈ B := by
  constructor
  · rintro ⟨z, rfl⟩ n
    rw [ModularCurve.coeffMap_coeff]
    exact (z.coeff n).2
  · intro h
    let z : LaurentSeries B :=
      { coeff := fun n => ⟨y.coeff n, h n⟩
        isPWO_support' := by
          have hs : (Function.support fun n => (⟨y.coeff n, h n⟩ : B)) = y.support := by
            ext n
            simp only [Function.mem_support, ne_eq, HahnSeries.mem_support]
            exact not_congr (Subtype.ext_iff.trans Iff.rfl)
          rw [hs]
          exact y.isPWO_support }
    exact ⟨z, HahnSeries.ext (funext fun n => rfl)⟩

theorem CB_mono {B B' : Subalgebra A R} (h : B ≤ B') : CB B ≤ CB B' := fun y hy =>
  (mem_CB_iff B' y).mpr fun n => h ((mem_CB_iff B y).mp hy n)

theorem single_mem_CB {B : Subalgebra A R} (k : ℤ) {r : R} (hr : r ∈ B) : single k r ∈ CB B := by
  refine (mem_CB_iff B _).mpr fun n => ?_
  rw [HahnSeries.coeff_single]
  split_ifs
  · exact hr
  · exact B.zero_mem

theorem C_mem_CB {B : Subalgebra A R} {r : R} (hr : r ∈ B) : HahnSeries.C r ∈ CB B := by
  rw [HahnSeries.C_apply]
  exact single_mem_CB 0 hr

theorem coeff_ofPowerSeries (F : PowerSeries R) (k : ℤ) :
    (ofPowerSeries ℤ R F).coeff k = if 0 ≤ k then PowerSeries.coeff k.toNat F else 0 := by
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [ofPowerSeries_apply_coeff, Int.toNat_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_range]
    intro h
    simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Nat.castOrderEmbedding_apply] at h
    obtain ⟨n, hn⟩ := h
    omega

theorem ofPowerSeries_mem_CB {B : Subalgebra A R} {F : PowerSeries R}
    (hF : ∀ n, PowerSeries.coeff n F ∈ B) : ofPowerSeries ℤ R F ∈ CB B := by
  refine (mem_CB_iff B _).mpr fun k => ?_
  rw [coeff_ofPowerSeries]
  split_ifs
  · exact hF _
  · exact B.zero_mem

theorem isUnit_map_of_mem_CB (B : Subalgebra A R) (x : LaurentSeries A) {z : LaurentSeries R}
    (hz : z ∈ CB B) (h : x.map (algebraMap A R) * z = 1) : IsUnit (x.map (algebraMap A B)) := by
  obtain ⟨zB, rfl⟩ := hz
  have hinj : Function.Injective (ModularCurve.coeffMap (algebraMap B R)) := fun a b hab =>
    HahnSeries.ext (funext fun k => Subtype.val_injective (by
      have := congrArg (fun y : LaurentSeries R => y.coeff k) hab
      simp only [ModularCurve.coeffMap_coeff] at this
      exact this))
  have hx : ModularCurve.coeffMap (algebraMap B R) (x.map (algebraMap A B)) = x.map (algebraMap A R) := by
    refine HahnSeries.ext (funext fun k => ?_)
    show algebraMap B R (algebraMap A B (x.coeff k)) = algebraMap A R (x.coeff k)
    exact (IsScalarTower.algebraMap_apply A B R _).symm
  refine IsUnit.of_mul_eq_one zB (hinj ?_)
  rw [map_mul, hx, h, map_one]

theorem exists_mul_eq_X_pow [Nontrivial R] {F : PowerSeries R} (hF : IsUnit (ofPowerSeries ℤ R F)) :
    ∃ (Γ : PowerSeries R) (n : ℕ), 1 ≤ n ∧ F * Γ = PowerSeries.X ^ n := by
  set U : LaurentSeries R := ((hF.unit⁻¹ : (LaurentSeries R)ˣ) : LaurentSeries R) with hU
  have hFU : ofPowerSeries ℤ R F * U = 1 := hF.mul_val_inv
  have hkey : ofPowerSeries ℤ R (F * U.powerSeriesPart) = single (-U.order) 1 := by
    rw [map_mul, ofPowerSeries_powerSeriesPart, mul_left_comm, hFU, mul_one]
  have hnn : 0 ≤ -U.order := by
    by_contra hlt
    have h1 : (ofPowerSeries ℤ R (F * U.powerSeriesPart)).coeff (-U.order) = 1 := by
      rw [hkey, coeff_single_same]
    rw [coeff_ofPowerSeries, if_neg hlt] at h1
    exact zero_ne_one h1
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnn
  refine ⟨U.powerSeriesPart * PowerSeries.X, m + 1, Nat.le_add_left 1 m, ?_⟩
  have hFΓ : F * U.powerSeriesPart = PowerSeries.X ^ m := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := R)
    rw [hkey, hm, ofPowerSeries_X_pow]
  rw [← mul_assoc, hFΓ, pow_succ]

theorem coeff_mul_range {F Γ : PowerSeries R} (j : ℕ) :
    PowerSeries.coeff j (F * Γ) =
      PowerSeries.constantCoeff F * PowerSeries.coeff j Γ +
        ∑ i ∈ Finset.range j, PowerSeries.coeff (i + 1) F * PowerSeries.coeff (j - (i + 1)) Γ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, tsub_zero]
  rw [add_comm]

theorem rel_of_mul_eq_X_pow {F Γ : PowerSeries R} {n : ℕ} (h : F * Γ = PowerSeries.X ^ n) :
    (∀ j < n, PowerSeries.constantCoeff F ^ (j + 1) * PowerSeries.coeff j Γ = 0) ∧
      PowerSeries.constantCoeff F ^ n = PowerSeries.constantCoeff F ^ (n + 1) * PowerSeries.coeff n Γ := by
  set a := PowerSeries.constantCoeff F with ha
  have hlow : ∀ j < n, PowerSeries.constantCoeff F ^ (j + 1) * PowerSeries.coeff j Γ = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hc : PowerSeries.coeff j (F * Γ) = 0 := by
        rw [h, PowerSeries.coeff_X_pow, if_neg (Nat.ne_of_lt hj)]
      rw [coeff_mul_range] at hc

      have hc' := congrArg (fun t => a ^ j * t) hc
      simp only [mul_zero, mul_add, Finset.mul_sum] at hc'
      have hsum : ∑ i ∈ Finset.range j, a ^ j * (PowerSeries.coeff (i + 1) F * PowerSeries.coeff (j - (i + 1)) Γ) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi' : i < j := Finset.mem_range.mp hi
        have hij : j - (i + 1) < j := by omega
        have hIH := ih (j - (i + 1)) hij (lt_trans hij hj)
        have hsplit : a ^ j = a ^ i * a ^ (j - (i + 1) + 1) := by
          rw [← _root_.pow_add]; congr 1; omega
        rw [hsplit]
        calc a ^ i * a ^ (j - (i + 1) + 1) * (PowerSeries.coeff (i + 1) F * PowerSeries.coeff (j - (i + 1)) Γ)
            = a ^ i * PowerSeries.coeff (i + 1) F *
                (a ^ (j - (i + 1) + 1) * PowerSeries.coeff (j - (i + 1)) Γ) := by ring
          _ = 0 := by rw [hIH, mul_zero]
      rw [hsum, add_zero, ← mul_assoc, ← pow_succ] at hc'
      exact hc'
  refine ⟨hlow, ?_⟩
  have hc : PowerSeries.coeff n (F * Γ) = 1 := by
    rw [h, PowerSeries.coeff_X_pow, if_pos rfl]
  rw [coeff_mul_range] at hc
  have hc' := congrArg (fun t => a ^ n * t) hc
  simp only [mul_one, mul_add, Finset.mul_sum] at hc'
  have hsum : ∑ i ∈ Finset.range n, a ^ n * (PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n - (i + 1)) Γ) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have hIH := hlow (n - (i + 1)) (by omega)
    have hsplit : a ^ n = a ^ i * a ^ (n - (i + 1) + 1) := by
      rw [← _root_.pow_add]; congr 1; omega
    rw [hsplit]
    calc a ^ i * a ^ (n - (i + 1) + 1) * (PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n - (i + 1)) Γ)
        = a ^ i * PowerSeries.coeff (i + 1) F *
            (a ^ (n - (i + 1) + 1) * PowerSeries.coeff (n - (i + 1)) Γ) := by ring
      _ = 0 := by rw [hIH, mul_zero]
  rw [hsum, add_zero, ← mul_assoc, ← pow_succ] at hc'
  exact hc'.symm

theorem idempotent_of_rel {a γ : R} {n : ℕ} (hn : 1 ≤ n) (h : a ^ n = a ^ (n + 1) * γ) :
    (a * γ) ^ n * (a * γ) ^ n = (a * γ) ^ n ∧ a * (a ^ (n - 1) * γ ^ n) = (a * γ) ^ n ∧
      a ^ n * (1 - (a * γ) ^ n) = 0 := by
  have hu : a ^ n * (a * γ) = a ^ n := by rw [← mul_assoc, ← pow_succ, ← h]
  have huk : ∀ k : ℕ, a ^ n * (a * γ) ^ k = a ^ n := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one]
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hu]
  refine ⟨?_, ?_, ?_⟩
  · calc (a * γ) ^ n * (a * γ) ^ n = γ ^ n * (a ^ n * (a * γ) ^ n) := by rw [mul_pow]; ring
      _ = (a * γ) ^ n := by rw [huk, mul_pow]; ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, mul_pow]
    ring
  · rw [mul_sub, mul_one, huk, sub_self]

def OrdLE (F : PowerSeries R) (m : ℕ) : Prop :=
  ∀ P : Ideal R, P.IsPrime → ∃ j ≤ m, PowerSeries.coeff j F ∉ P

theorem ordLE_of_mul_eq_X_pow {F Γ : PowerSeries R} {n : ℕ} (h : F * Γ = PowerSeries.X ^ n) :
    OrdLE F n := by
  intro P hP
  by_contra hall
  push Not at hall
  have hc : PowerSeries.coeff n (F * Γ) = 1 := by rw [h, PowerSeries.coeff_X_pow, if_pos rfl]
  have hmem : PowerSeries.coeff n (F * Γ) ∈ P := by
    rw [PowerSeries.coeff_mul]
    refine P.sum_mem fun ij hij => ?_
    have hle : ij.1 ≤ n := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      omega
    exact P.mul_mem_right _ (hall ij.1 hle)
  rw [hc] at hmem
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr hmem)

theorem isUnit_of_ordLE_zero {F : PowerSeries R} (h : OrdLE F 0) : IsUnit (PowerSeries.constantCoeff F) := by
  by_contra hu
  obtain ⟨M, hM, haM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
  obtain ⟨j, hj, hjM⟩ := h M hM.isPrime
  obtain rfl : j = 0 := Nat.le_zero.mp hj
  exact hjM (by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply])

def shiftPS (F : PowerSeries R) : PowerSeries R := PowerSeries.mk fun j => PowerSeries.coeff (j + 1) F

def stepPS (F : PowerSeries R) (e : R) : PowerSeries R :=
  PowerSeries.mk fun j => (if j = 0 then e else 0) + (1 - e) * PowerSeries.coeff (j + 1) F

theorem coeff_stepPS (F : PowerSeries R) (e : R) (j : ℕ) :
    PowerSeries.coeff j (stepPS F e) = (if j = 0 then e else 0) + (1 - e) * PowerSeries.coeff (j + 1) F :=
  PowerSeries.coeff_mk _ _

theorem F_eq (F : PowerSeries R) :
    F = PowerSeries.X * shiftPS F + PowerSeries.C (PowerSeries.constantCoeff F) :=
  PowerSeries.eq_X_mul_shift_add_const F

theorem stepPS_eq (F : PowerSeries R) (e : R) :
    stepPS F e = PowerSeries.C e + PowerSeries.C (1 - e) * shiftPS F := by
  ext j
  rw [coeff_stepPS, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, shiftPS, PowerSeries.coeff_mk]

theorem one_sub_pow_succ {e : R} (he : e * e = e) (k : ℕ) : (1 - e) ^ (k + 1) = 1 - e := by
  induction k with
  | zero => rw [pow_one]
  | succ k ih =>
    rw [pow_succ, ih]
    linear_combination he

theorem ordLE_stepPS {F : PowerSeries R} {m : ℕ} (hF : OrdLE F (m + 1)) {e : R} (he : e * e = e)
    {N : ℕ} (haN : PowerSeries.constantCoeff F ^ N * (1 - e) = 0) : OrdLE (stepPS F e) m := by
  intro P hP
  by_cases heP : e ∈ P
  ·
    have h1e : 1 - e ∉ P := fun h =>
      hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using P.add_mem h heP))
    have haP : PowerSeries.constantCoeff F ∈ P := by
      have h0 : PowerSeries.constantCoeff F ^ N * (1 - e) ∈ P := by rw [haN]; exact P.zero_mem
      rcases hP.mem_or_mem h0 with h | h
      · exact hP.mem_of_pow_mem N h
      · exact absurd h h1e
    obtain ⟨j, hj, hjP⟩ := hF P hP
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
      rcases j with _ | j'
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hjP
        exact absurd haP hjP
      · exact ⟨j', rfl⟩
    refine ⟨j', by omega, fun hmem => hjP ?_⟩
    rw [coeff_stepPS] at hmem
    have hite : (if j' = 0 then e else 0) ∈ P := by
      split_ifs
      · exact heP
      · exact P.zero_mem
    have h2 : (1 - e) * PowerSeries.coeff (j' + 1) F ∈ P := by simpa using P.sub_mem hmem hite
    rcases hP.mem_or_mem h2 with h | h
    · exact absurd h h1e
    · exact h
  ·
    have h1e : 1 - e ∈ P := by
      have h0 : e * (1 - e) ∈ P := by rw [mul_sub, mul_one, he, sub_self]; exact P.zero_mem
      rcases hP.mem_or_mem h0 with h | h
      · exact absurd h heP
      · exact h
    refine ⟨0, Nat.zero_le _, fun hmem => heP ?_⟩
    rw [coeff_stepPS, if_pos rfl] at hmem
    have h2 : (1 - e) * PowerSeries.coeff (0 + 1) F ∈ P := P.mul_mem_right _ h1e
    simpa using P.sub_mem hmem h2

theorem isUnit_ofPowerSeries_stepPS {F : PowerSeries R} (hF : IsUnit (ofPowerSeries ℤ R F)) {e : R}
    (he : e * e = e) {N : ℕ} (haN : PowerSeries.constantCoeff F ^ N * (1 - e) = 0) :
    IsUnit (ofPowerSeries ℤ R (stepPS F e)) := by
  set f : LaurentSeries R := ofPowerSeries ℤ R F with hfdef
  set fs : LaurentSeries R := ofPowerSeries ℤ R (shiftPS F) with hfsdef
  set a : R := PowerSeries.constantCoeff F with ha
  set U : LaurentSeries R := ((hF.unit⁻¹ : (LaurentSeries R)ˣ) : LaurentSeries R) with hU
  have hfU : f * U = 1 := hF.mul_val_inv
  set cE : LaurentSeries R := HahnSeries.C e with hcE
  set cA : LaurentSeries R := HahnSeries.C a with hcA
  set q : LaurentSeries R := single 1 1 with hq
  have hf : f = cA + q * fs := by
    rw [hfdef, hfsdef, hcA, hq]
    conv_lhs => rw [F_eq F]
    rw [map_add, map_mul, ofPowerSeries_X, ofPowerSeries_C, add_comm]
  have hf' : ofPowerSeries ℤ R (stepPS F e) = cE + (1 - cE) * fs := by
    rw [stepPS_eq, map_add, map_mul, ofPowerSeries_C, ofPowerSeries_C, map_sub, map_one]
  have hE : cE * cE = cE := by rw [hcE, ← map_mul, he]
  have hNR : ((1 - e) * a) ^ (N + 1) = 0 := by
    rw [mul_pow, one_sub_pow_succ he, pow_succ, ← mul_assoc, mul_comm (1 - e) (a ^ N), haN, zero_mul]
  have hN : ((1 - cE) * cA) ^ (N + 1) = 0 := by
    have h1 : (1 - cE) * cA = HahnSeries.C ((1 - e) * a) := by rw [map_mul, map_sub, map_one]
    rw [h1, ← map_pow, hNR, map_zero]
  set W : LaurentSeries R := ∑ i ∈ Finset.range (N + 1), ((1 - cE) * cA * U) ^ i with hW
  have hgeom : (1 - (1 - cE) * cA * U) * W = 1 - ((1 - cE) * cA * U) ^ (N + 1) := mul_neg_geom_sum _ _
  have h4 : ((1 - cE) * cA * U) ^ (N + 1) = 0 := by rw [mul_pow, hN, zero_mul]
  refine IsUnit.of_mul_eq_one (cE + (1 - cE) * q * U * W) ?_
  rw [hf']
  rw [hf] at hfU
  set T := ((1 - cE) * cA * U) ^ (N + 1) with hT
  linear_combination (cA * U * W + 1 - q * U * W - fs + fs * q * U * W) * hE + ((1 - cE) * W) * hfU +
    (1 - cE) * hgeom - (1 - cE) * h4

theorem exists_inv_of_constantCoeff {B : Subalgebra A R} {H : PowerSeries R}
    (hH : ∀ j, PowerSeries.coeff j H ∈ B) {b : R} (hb : b ∈ B) (h1 : PowerSeries.constantCoeff H * b = 1) :
    ∃ z ∈ CB B, ofPowerSeries ℤ R H * z = 1 := by
  let HB : PowerSeries B := PowerSeries.mk fun j => ⟨PowerSeries.coeff j H, hH j⟩
  have hmap : HB.map (algebraMap B R) = H := by
    ext j
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hc0 : ((PowerSeries.constantCoeff HB : B) : R) = PowerSeries.constantCoeff H := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    show ((PowerSeries.coeff 0 (PowerSeries.mk fun j => (⟨PowerSeries.coeff j H, hH j⟩ : B)) : B) : R) = _
    rw [PowerSeries.coeff_mk]
  have hunit : IsUnit (PowerSeries.constantCoeff HB) := by
    refine IsUnit.of_mul_eq_one ⟨b, hb⟩ (Subtype.ext ?_)
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, hc0]
    exact h1
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr hunit
  refine ⟨ofPowerSeries ℤ R (((u⁻¹ : (PowerSeries B)ˣ) : PowerSeries B).map (algebraMap B R)),
    ofPowerSeries_mem_CB fun j => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]
    exact Subtype.mem _
  · rw [← map_mul (ofPowerSeries ℤ R), ← hmap, ← map_mul (PowerSeries.map (algebraMap B R)), ← hu,
      Units.mul_inv, map_one, map_one]

theorem core [Nontrivial R] (m : ℕ) : ∀ (S₀ : Finset R) (F : PowerSeries R),
    (∀ j, PowerSeries.coeff j F ∈ Algebra.adjoin A (S₀ : Set R)) → IsUnit (ofPowerSeries ℤ R F) →
    OrdLE F m →
    ∃ (S : Finset R) (z : LaurentSeries R), z ∈ CB (Algebra.adjoin A (S : Set R)) ∧
      ofPowerSeries ℤ R F * z = 1 := by
  classical
  induction m with
  | zero =>
    intro S₀ F hF hunit hord
    obtain ⟨u, hu⟩ := isUnit_of_ordLE_zero hord
    let S : Finset R := S₀ ∪ {((u⁻¹ : Rˣ) : R)}
    have hmono : Algebra.adjoin A (S₀ : Set R) ≤ Algebra.adjoin A (S : Set R) :=
      Algebra.adjoin_mono (by simp [S])
    obtain ⟨z, hz, hz1⟩ := exists_inv_of_constantCoeff (B := Algebra.adjoin A (S : Set R)) (H := F)
      (fun j => hmono (hF j)) (b := ((u⁻¹ : Rˣ) : R)) (Algebra.subset_adjoin (by simp [S]))
      (by rw [← hu]; exact u.mul_inv)
    exact ⟨S, z, hz, hz1⟩
  | succ m ih =>
    intro S₀ F hF hunit hord
    obtain ⟨Γ, n, hn, hFΓ⟩ := exists_mul_eq_X_pow hunit
    obtain ⟨-, hrel⟩ := rel_of_mul_eq_X_pow hFΓ
    obtain ⟨he, haa', haN⟩ := idempotent_of_rel hn hrel
    set a := PowerSeries.constantCoeff F with ha
    set γ := PowerSeries.coeff n Γ with hγ
    set e := (a * γ) ^ n with hedef
    set a' := a ^ (n - 1) * γ ^ n with ha'def

    let S₁ : Finset R := S₀ ∪ {γ}
    have hB01 : Algebra.adjoin A (S₀ : Set R) ≤ Algebra.adjoin A (S₁ : Set R) :=
      Algebra.adjoin_mono (by simp [S₁])
    have haB : a ∈ Algebra.adjoin A (S₁ : Set R) := by
      refine hB01 ?_
      rw [ha, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hF 0
    have hγB : γ ∈ Algebra.adjoin A (S₁ : Set R) := Algebra.subset_adjoin (by simp [S₁])
    have heB : e ∈ Algebra.adjoin A (S₁ : Set R) := Subalgebra.pow_mem _ (Subalgebra.mul_mem _ haB hγB) _
    have ha'B : a' ∈ Algebra.adjoin A (S₁ : Set R) :=
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ haB _) (Subalgebra.pow_mem _ hγB _)

    have hF' : ∀ j, PowerSeries.coeff j (stepPS F e) ∈ Algebra.adjoin A (S₁ : Set R) := by
      intro j
      rw [coeff_stepPS]
      refine Subalgebra.add_mem _ ?_
        (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) heB) (hB01 (hF _)))
      split_ifs
      · exact heB
      · exact Subalgebra.zero_mem _
    have hunit' := isUnit_ofPowerSeries_stepPS hunit he haN
    have hord' := ordLE_stepPS hord he haN
    obtain ⟨S, z', hz', hFz'⟩ := ih S₁ (stepPS F e) hF' hunit' hord'

    let S₂ : Finset R := S₁ ∪ S
    set B := Algebra.adjoin A (S₂ : Set R) with hBdef
    have h1B : Algebra.adjoin A (S₁ : Set R) ≤ B := Algebra.adjoin_mono (by simp [S₂])
    have h2B : Algebra.adjoin A (S : Set R) ≤ B := Algebra.adjoin_mono (by simp [S₂])
    refine ⟨S₂, ?_⟩

    obtain ⟨z₁, hz₁, hz₁1⟩ := exists_inv_of_constantCoeff (B := B) (H := PowerSeries.C e * F + PowerSeries.C (1 - e))
      (fun j => by
        rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C]
        refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (h1B heB) (h1B (hB01 (hF j)))) ?_
        split_ifs
        · exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) (h1B heB)
        · exact Subalgebra.zero_mem _)
      (b := e * a' + (1 - e))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (h1B heB) (h1B ha'B))
        (Subalgebra.sub_mem _ (Subalgebra.one_mem _) (h1B heB)))
      (by
        have hc : PowerSeries.constantCoeff (PowerSeries.C e * F + PowerSeries.C (1 - e)) = e * a + (1 - e) := by
          rw [map_add, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C]
        rw [hc]
        linear_combination (e ^ 2) * haa' + (e + 2 - a - a') * he)

    set f : LaurentSeries R := ofPowerSeries ℤ R F with hfdef
    set f' : LaurentSeries R := ofPowerSeries ℤ R (stepPS F e) with hf'def
    set fs : LaurentSeries R := ofPowerSeries ℤ R (shiftPS F) with hfsdef
    set cE : LaurentSeries R := HahnSeries.C e with hcE
    set cA : LaurentSeries R := HahnSeries.C a with hcA
    set q : LaurentSeries R := single 1 1 with hq
    set qi : LaurentSeries R := single (-1) 1 with hqi
    have hf : f = cA + q * fs := by
      rw [hfdef, hfsdef, hcA, hq]
      conv_lhs => rw [F_eq F]
      rw [map_add, map_mul, ofPowerSeries_X, ofPowerSeries_C, add_comm]
    have hf'eq : f' = cE + (1 - cE) * fs := by
      rw [hf'def, stepPS_eq, map_add, map_mul, ofPowerSeries_C, ofPowerSeries_C, map_sub, map_one]
    have hE : cE * cE = cE := by rw [hcE, ← map_mul, he]
    have hqq : q * qi = 1 := by rw [hq, hqi, single_mul_single, add_neg_cancel, mul_one, single_zero_one]
    have hs2 : (1 - cE) * (1 - cE) = 1 - cE := by linear_combination hE
    have hsE : (1 - cE) * cE = 0 := by linear_combination -hE
    have h_sf' : (1 - cE) * f' = (1 - cE) * fs := by
      rw [hf'eq]
      linear_combination fs * hs2 + hsE
    have h_sf : (1 - cE) * f = (1 - cE) * cA + q * ((1 - cE) * fs) := by
      rw [hf]
      ring

    set z₂ : LaurentSeries R := ((1 - cE) * z' + cE) * ((1 - cE) * qi + cE) with hz₂
    have hp1 : ((1 - cE) * f' + cE) * ((1 - cE) * z' + cE) = 1 := by
      linear_combination ((1 - cE) ^ 2) * hFz' + (2 - f' - z') * hE
    have hp2 : ((1 - cE) * q + cE) * ((1 - cE) * qi + cE) = 1 := by
      linear_combination ((1 - cE) ^ 2) * hqq + (2 - q - qi) * hE
    have hT : ((1 - cE) * f' + cE) * ((1 - cE) * q + cE) * z₂ = 1 := by
      calc ((1 - cE) * f' + cE) * ((1 - cE) * q + cE) * z₂
          = (((1 - cE) * f' + cE) * ((1 - cE) * z' + cE)) * (((1 - cE) * q + cE) * ((1 - cE) * qi + cE)) := by
            rw [hz₂]; ring
        _ = 1 := by rw [hp1, hp2, one_mul]
    have hTeq : ((1 - cE) * f' + cE) * ((1 - cE) * q + cE) = q * ((1 - cE) * fs) + cE := by
      linear_combination ((1 - cE) * q + cE) * h_sf' + (fs * q) * hs2 + (fs + q) * hsE + hE
    have hNT : (1 - cE) * cA + ((1 - cE) * f' + cE) * ((1 - cE) * q + cE) = (1 - cE) * f + cE := by
      rw [hTeq, h_sf]
      ring

    have hNn : ((1 - cE) * cA) ^ n = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hR : ((1 - e) * a) ^ (k + 1) = 0 := by
        rw [mul_pow, one_sub_pow_succ he, mul_comm, haN]
      have h1 : (1 - cE) * cA = HahnSeries.C ((1 - e) * a) := by rw [map_mul, map_sub, map_one]
      rw [h1, ← map_pow, hR, map_zero]
    set xN : LaurentSeries R := -((1 - cE) * cA * z₂) with hxN
    set G : LaurentSeries R := ∑ i ∈ Finset.range n, xN ^ i with hG
    have hgeom : (1 - xN) * G = 1 - xN ^ n := mul_neg_geom_sum _ _
    have hxn : xN ^ n = 0 := by rw [hxN, neg_pow, mul_pow, hNn, zero_mul, mul_zero]
    set z₃ : LaurentSeries R := z₂ * G with hz₃
    have hz₃1 : ((1 - cE) * f + cE) * z₃ = 1 := by
      rw [← hNT, hz₃, ← mul_assoc, add_mul, hT]
      have h : ((1 - cE) * cA * z₂ + 1) = 1 - xN := by rw [hxN]; ring
      rw [h, hgeom, hxn, sub_zero]

    have hz₁1' : (cE * f + (1 - cE)) * z₁ = 1 := by
      have h := hz₁1
      rw [map_add, map_mul, ofPowerSeries_C, ofPowerSeries_C, map_sub, map_one] at h
      exact h
    have hfac : f = (cE * f + (1 - cE)) * ((1 - cE) * f + cE) := by
      linear_combination (f ^ 2 - 2 * f + 1) * hE
    refine ⟨z₁ * z₃, Subring.mul_mem _ hz₁ ?_, ?_⟩
    ·
      have hcE : cE ∈ CB B := C_mem_CB (h1B heB)
      have hcA : cA ∈ CB B := C_mem_CB (h1B haB)
      have hz'B : z' ∈ CB B := CB_mono h2B hz'
      have hqiB : qi ∈ CB B := single_mem_CB _ (Subalgebra.one_mem _)
      have hone : (1 : LaurentSeries R) ∈ CB B := Subring.one_mem _
      have hz₂B : z₂ ∈ CB B :=
        Subring.mul_mem _ (Subring.add_mem _ (Subring.mul_mem _ (Subring.sub_mem _ hone hcE) hz'B) hcE)
          (Subring.add_mem _ (Subring.mul_mem _ (Subring.sub_mem _ hone hcE) hqiB) hcE)
      have hxNB : xN ∈ CB B :=
        Subring.neg_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (Subring.sub_mem _ hone hcE) hcA) hz₂B)
      exact Subring.mul_mem _ hz₂B (Subring.sum_mem _ fun i _ => Subring.pow_mem _ hxNB i)
    · calc f * (z₁ * z₃) = ((cE * f + (1 - cE)) * z₁) * (((1 - cE) * f + cE) * z₃) := by
            conv_lhs => rw [hfac]
            ring
        _ = 1 := by rw [hz₁1', hz₃1, one_mul]

end LaurentSeries.UnitDescent

end

open HahnSeries LaurentSeries.UnitDescent in
theorem solution
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (x : LaurentSeries A) (hx : IsUnit (x.map (algebraMap A R))) :
    ∃ B : Subalgebra A R, B.FG ∧ IsUnit (x.map (algebraMap A B)) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨⊥, Subalgebra.fg_bot, ?_⟩
    haveI : Subsingleton (⊥ : Subalgebra A R) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact isUnit_of_subsingleton _
  set xR : LaurentSeries R := x.map (algebraMap A R) with hxR
  set F : PowerSeries R := xR.powerSeriesPart with hFdef
  have hcoef : ∀ j, PowerSeries.coeff j F ∈ Algebra.adjoin A ((∅ : Finset R) : Set R) := by
    intro j
    rw [hFdef, LaurentSeries.powerSeriesPart_coeff]
    exact Subalgebra.algebraMap_mem _ _
  have hunit : IsUnit (ofPowerSeries ℤ R F) := by
    rw [hFdef, LaurentSeries.ofPowerSeries_powerSeriesPart]
    refine IsUnit.mul (IsUnit.of_mul_eq_one (single xR.order 1) ?_) hx
    rw [single_mul_single, neg_add_cancel, mul_one, single_zero_one]
  obtain ⟨Γ, n, -, hFΓ⟩ := exists_mul_eq_X_pow hunit
  obtain ⟨S, z, hz, hFz⟩ := core n ∅ F hcoef hunit (ordLE_of_mul_eq_X_pow hFΓ)
  refine ⟨Algebra.adjoin A (S : Set R), ⟨S, rfl⟩, ?_⟩
  refine isUnit_map_of_mem_CB _ x (z := single (-xR.order) 1 * z)
    (Subring.mul_mem _ (single_mem_CB _ (Subalgebra.one_mem _)) hz) ?_
  show xR * (single (-xR.order) 1 * z) = 1
  rw [← mul_assoc, mul_comm xR, ← LaurentSeries.ofPowerSeries_powerSeriesPart, ← hFdef, hFz]

end S_LaurentSeries_exists_fg_subalgebra_isUnit_map_of_isUnit_map
end P2MW
export P2MW.S_LaurentSeries_exists_fg_subalgebra_isUnit_map_of_isUnit_map (solution)
