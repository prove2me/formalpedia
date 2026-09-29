-- Prove2me | solution 1 for ModularCurve.mem_adjoin_lambdaModC_of_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1dccaf2f-274e-5081-b764-680128220dce

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_adjoin_lambdaModC_of_pow_mul_mem
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve Polynomial

namespace LambdaE2Sol

section Supp

variable {R : Type*} [CommRing R]

def SuppGE (n : ℤ) (x : LaurentSeries R) : Prop := ∀ k < n, x.coeff k = 0

namespace SuppGE

variable {n a b : ℤ} {x y : LaurentSeries R}

theorem mono {m : ℤ} (h : m ≤ n) (hx : SuppGE n x) : SuppGE m x := fun k hk => hx k (lt_of_lt_of_le hk h)

theorem add (hx : SuppGE n x) (hy : SuppGE n y) : SuppGE n (x + y) :=
  fun k hk => by rw [HahnSeries.coeff_add, hx k hk, hy k hk, add_zero]

theorem neg (hx : SuppGE n x) : SuppGE n (-x) :=
  fun k hk => by rw [HahnSeries.coeff_neg, hx k hk, neg_zero]

theorem sub (hx : SuppGE n x) (hy : SuppGE n y) : SuppGE n (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem single' (m : ℤ) (r : R) : SuppGE m (HahnSeries.single m r) :=
  fun k hk => HahnSeries.coeff_single_of_ne (ne_of_lt hk)

theorem C' (r : R) : SuppGE 0 (HahnSeries.C r : LaurentSeries R) := single' 0 r

theorem one' : SuppGE 0 (1 : LaurentSeries R) := by
  have h := C' (1 : R)
  rwa [map_one] at h

theorem ofNat' (m : ℕ) [m.AtLeastTwo] : SuppGE 0 (OfNat.ofNat m : LaurentSeries R) := by
  have h := C' (R := R) (OfNat.ofNat m)
  rwa [map_ofNat] at h

theorem mul (hx : SuppGE a x) (hy : SuppGE b y) : SuppGE (a + b) (x * y) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun ij hij => ?_)
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  rw [HahnSeries.mem_support] at h1 h2
  have ha : a ≤ ij.1 := not_lt.mp (fun hlt => h1 (hx _ hlt))
  have hb : b ≤ ij.2 := not_lt.mp (fun hlt => h2 (hy _ hlt))
  omega

theorem pow (hx : SuppGE a x) : ∀ m : ℕ, SuppGE (m * a) (x ^ m)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_mul]; exact one'
  | m + 1 => by rw [pow_succ, Nat.cast_succ, add_mul, one_mul]; exact (pow hx m).mul hx

theorem pow0 (hx : SuppGE 0 x) (m : ℕ) : SuppGE 0 (x ^ m) := by simpa using hx.pow m

theorem qExpand' (hx : SuppGE a x) (N : ℕ) [NeZero N] : SuppGE (N * a) (ModularCurve.qExpand R N x) := by
  intro k hk
  by_cases hd : (N : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    refine hx k' ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact lt_of_mul_lt_mul_left hk hN.le
  · exact qExpand_coeff_of_not_dvd N x hd

theorem laurentMap' (hx : SuppGE a x) {S : Type*} [CommRing S] (f : R →+* S) :
    SuppGE a (ModularCurve.laurentMap f x) :=
  fun k hk => by rw [laurentMap_coeff, hx k hk, map_zero]

theorem ofPowerSeries' (p : PowerSeries R) : SuppGE 0 (HahnSeries.ofPowerSeries ℤ R p) :=
  fun k hk => ofPowerSeries_coeff_of_neg p hk

end SuppGE

theorem coeff_mul_of_suppGE {a b : ℤ} {x y : LaurentSeries R} (hx : SuppGE a x) (hy : SuppGE b y) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  rw [HahnSeries.coeff_mul, Finset.sum_eq_single (a, b)]
  · intro ij hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    rw [HahnSeries.mem_support] at h1 h2
    have ha : a ≤ ij.1 := not_lt.mp (fun hlt => h1 (hx _ hlt))
    have hb : b ≤ ij.2 := not_lt.mp (fun hlt => h2 (hy _ hlt))
    exfalso
    apply hne
    refine Prod.ext ?_ ?_
    · show ij.1 = a
      omega
    · show ij.2 = b
      omega
  · intro hn
    rw [Finset.mem_antidiagonal, not_and, not_and] at hn
    by_cases hxa : x.coeff a = 0
    · rw [hxa, zero_mul]
    by_cases hyb : y.coeff b = 0
    · rw [hyb, mul_zero]
    exact absurd rfl (hn (by rw [HahnSeries.mem_support]; exact hxa) (by rw [HahnSeries.mem_support]; exact hyb))

theorem coeff_pow_of_suppGE_zero {x : LaurentSeries R} (hx : SuppGE 0 x) :
    ∀ m : ℕ, (x ^ m).coeff 0 = (x.coeff 0) ^ m
  | 0 => by
      rw [pow_zero, pow_zero]
      have h : (HahnSeries.C (1 : R) : LaurentSeries R).coeff 0 = 1 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rwa [map_one] at h
  | m + 1 => by
      rw [pow_succ, pow_succ, ← coeff_pow_of_suppGE_zero hx m]
      have h := coeff_mul_of_suppGE (hx.pow0 m) hx
      rwa [add_zero] at h

theorem coeff_C_zero (r : R) : (HahnSeries.C r : LaurentSeries R).coeff 0 = r := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem coeff_one_zero : (1 : LaurentSeries R).coeff 0 = 1 := by
  have h := coeff_C_zero (1 : R); rwa [map_one] at h

theorem coeff_ofNat_zero (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : LaurentSeries R).coeff 0 = (OfNat.ofNat m : R) := by
  have h := coeff_C_zero (R := R) (OfNat.ofNat m); rwa [map_ofNat] at h

theorem coeff_zero_of_suppGE_one {x : LaurentSeries R} (hx : SuppGE 1 x) : x.coeff 0 = 0 := hx 0 zero_lt_one

end Supp

section Expansions

theorem suppGE_lambdaInt_and_coeff : SuppGE 1 lambdaInt ∧ lambdaInt.coeff 1 = 1 := by

  set A : LaurentSeries ℤ := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 with hA
  set X : LaurentSeries ℤ := qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) with hX
  set Y : LaurentSeries ℤ := qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) with hY
  have hdef : lambdaInt = HahnSeries.single 1 1 * (A * (X * Y)) := by
    rw [lambdaInt]; simp only [mul_assoc, hA, hX, hY]
  have hE : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := SuppGE.ofPowerSeries' _
  have hE0 : (HahnSeries.ofPowerSeries ℤ ℤ etaProd).coeff 0 = 1 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd]
  have hAs : SuppGE 0 A := hE.pow0 8
  have hA0 : A.coeff 0 = 1 := by rw [hA, coeff_pow_of_suppGE_zero hE, hE0, one_pow]
  have hXs : SuppGE 0 X := by rw [hX]; simpa using (hE.pow0 16).qExpand' 4
  have hX0 : X.coeff 0 = 1 := by
    have h := qExpand_coeff_mul 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) 0
    rw [mul_zero] at h
    rw [hX, h, coeff_pow_of_suppGE_zero hE, hE0, one_pow]
  have hD : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := SuppGE.ofPowerSeries' _
  have hYs : SuppGE 0 Y := by rw [hY]; simpa using hD.qExpand' 2
  have hY0 : Y.coeff 0 = 1 := by
    have h := qExpand_coeff_mul 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) 0
    rw [mul_zero] at h
    rw [hY, h, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnitInv]
  have hZs : SuppGE 0 (A * (X * Y)) := by simpa using hAs.mul (hXs.mul hYs)
  have hZ0 : (A * (X * Y)).coeff 0 = 1 := by
    have h1 := coeff_mul_of_suppGE hXs hYs
    rw [add_zero] at h1
    have h2 := coeff_mul_of_suppGE hAs (hXs.mul hYs)
    simp only [add_zero] at h2
    rw [h2, h1, hA0, hX0, hY0]; ring
  refine ⟨?_, ?_⟩
  · rw [hdef]
    have h := (SuppGE.single' (R := ℤ) 1 1).mul hZs
    rwa [add_zero] at h
  · rw [hdef]
    have h := coeff_mul_of_suppGE (SuppGE.single' (R := ℤ) 1 1) hZs
    rw [add_zero] at h
    rw [h, HahnSeries.coeff_single_same, hZ0, one_mul]

theorem suppGE_mu : SuppGE 1 (lambdaModC ℚ) :=
  suppGE_lambdaInt_and_coeff.1.laurentMap' _

theorem coeff_mu_one : (lambdaModC ℚ).coeff 1 = 1 := by
  show (laurentMap (Int.castRingHom ℚ) lambdaInt).coeff 1 = 1
  rw [laurentMap_coeff, suppGE_lambdaInt_and_coeff.2, map_one]

theorem coeff_mu_zero : (lambdaModC ℚ).coeff 0 = 0 := suppGE_mu 0 zero_lt_one

end Expansions

section MuPowers

theorem coeff_pow_of_suppGE {R : Type*} [CommRing R] {a : ℤ} {x : LaurentSeries R} (hx : SuppGE a x) :
    ∀ m : ℕ, (x ^ m).coeff (m * a) = (x.coeff a) ^ m
  | 0 => by
      rw [pow_zero, pow_zero, Nat.cast_zero, zero_mul]
      exact coeff_one_zero
  | m + 1 => by
      rw [pow_succ, pow_succ, ← coeff_pow_of_suppGE hx m, Nat.cast_succ, add_mul, one_mul]
      exact coeff_mul_of_suppGE (hx.pow m) hx

theorem suppGE_mu_pow (i : ℕ) : SuppGE (i : ℤ) (lambdaModC ℚ ^ i) := by
  simpa using suppGE_mu.pow i

theorem coeff_mu_pow_self (i : ℕ) : (lambdaModC ℚ ^ i).coeff (i : ℤ) = 1 := by
  have h := coeff_pow_of_suppGE suppGE_mu i
  rw [mul_one] at h
  rw [h, coeff_mu_one, one_pow]

theorem coeff_mu_pow_int (i : ℕ) (n : ℤ) : (lambdaModC ℚ ^ i).coeff n = ((lambdaInt ^ i).coeff n : ℚ) := by
  rw [lambdaModC, ← map_pow, laurentMap_coeff]
  rfl

theorem algebraMap_laurentSeries_eq_single (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c := by
  have h1 : algebraMap ℚ (PowerSeries ℚ) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

theorem coeff_aeval_mu (P : Polynomial ℚ) (k : ℕ) :
    (Polynomial.aeval (lambdaModC ℚ) P).coeff (k : ℤ)
      = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (lambdaModC ℚ ^ i).coeff (k : ℤ) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

theorem coeff_mu_pow_of_lt {i : ℕ} {k : ℤ} (hk : k < i) : (lambdaModC ℚ ^ i).coeff k = 0 :=
  suppGE_mu_pow i k hk

end MuPowers

theorem nopole0 (w : LaurentSeries ℚ) (hw : ∀ n : ℤ, n < 0 → w.coeff n = 0) (a : ℕ)
    (h : lambdaModC ℚ ^ a * w ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ))) :
    w ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h ⊢
  obtain ⟨P, hP⟩ := h
  change Polynomial.aeval (lambdaModC ℚ) P = lambdaModC ℚ ^ a * w at hP

  have hlow : ∀ d < a, P.coeff d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro hd

      have h1 : (Polynomial.aeval (lambdaModC ℚ) P).coeff (d : ℤ) = P.coeff d := by
        rw [coeff_aeval_mu]
        by_cases hdn : P.natDegree < d
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdn]
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [IH i (by omega) (by omega), zero_mul]
        push_neg at hdn
        rw [Finset.sum_eq_single d]
        · rw [coeff_mu_pow_self, mul_one]
        · intro i hi hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [IH i hlt (lt_trans hlt hd), zero_mul]
          · rw [coeff_mu_pow_of_lt (by exact_mod_cast hgt), mul_zero]
        · intro hn; exfalso; exact hn (Finset.mem_range.mpr (by omega))

      have h2 : (Polynomial.aeval (lambdaModC ℚ) P).coeff (d : ℤ) = 0 := by
        rw [hP]
        have hs : SuppGE ((a : ℤ) + 0) (lambdaModC ℚ ^ a * w) := (suppGE_mu_pow a).mul (fun n hn => hw n hn)
        exact hs d (by push_cast; omega)
      rw [← h1, h2]

  obtain ⟨P', hP'⟩ := (Polynomial.X_pow_dvd_iff).mpr hlow
  refine ⟨P', ?_⟩
  change Polynomial.aeval (lambdaModC ℚ) P' = w
  have hμ : lambdaModC ℚ ^ a ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := coeff_mu_one
    rw [h0, HahnSeries.coeff_zero] at this
    exact zero_ne_one this
  apply mul_left_cancel₀ hμ
  rw [← hP, hP', map_mul, map_pow, Polynomial.aeval_X]

end LambdaE2Sol

end

open ModularCurve LambdaE2Sol in
theorem solution (w : LaurentSeries ℚ)
    (hw : ∀ n : ℤ, n < 0 → w.coeff n = 0) (a : ℕ)
    (h : lambdaModC ℚ ^ a * w ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ))) :
    w ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) :=
  LambdaE2Sol.nopole0 w hw a h

end S_ModularCurve_mem_adjoin_lambdaModC_of_pow_mul_mem
end P2MW
export P2MW.S_ModularCurve_mem_adjoin_lambdaModC_of_pow_mul_mem (solution)
