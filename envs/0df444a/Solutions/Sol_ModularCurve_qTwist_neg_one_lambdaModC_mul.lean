-- Prove2me | solution 1 for ModularCurve.qTwist_neg_one_lambdaModC_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/af2a19e9-31bc-52ac-92a5-6278f3902065

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qTwist_neg_one_lambdaModC_mul
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
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

section Muneg

local notation "L" => LaurentSeries ℚ

theorem suppGE_v : SuppGE 1 (qTwist (-1 : ℚˣ) (lambdaModC ℚ)) :=
  fun k hk => by rw [qTwist_coeff, suppGE_mu k hk, mul_zero]

theorem coeff_v_one : (qTwist (-1 : ℚˣ) (lambdaModC ℚ)).coeff 1 = -1 := by
  rw [qTwist_coeff, coeff_mu_one, mul_one, zpow_one, Units.val_neg, Units.val_one]

theorem coeff_zero_ofNat_mul {x : L} (hx : SuppGE 1 x) (m : ℕ) [m.AtLeastTwo] :
    ((OfNat.ofNat m : L) * x).coeff 0 = 0 := by
  have h := (SuppGE.ofNat' (R := ℚ) m).mul hx
  rw [zero_add] at h
  exact coeff_zero_of_suppGE_one h

theorem muneg_rat :
    qTwist (-1 : ℚˣ) (lambdaModC ℚ) * (16 * lambdaModC ℚ - 1) = lambdaModC ℚ := by
  set u : L := lambdaModC ℚ with hu
  set v : L := qTwist (-1 : ℚˣ) (lambdaModC ℚ) with hv

  have hJΛ : qExpand ℚ 2 jq * u ^ 2 * (16 * u - 1) ^ 2 = (256 * u ^ 2 - 16 * u + 1) ^ 3 :=
    qExpand_two_jq_mul_lambdaModC_sq
  have heven : qTwist (-1 : ℚˣ) (qExpand ℚ 2 jq) = qExpand ℚ 2 jq := by
    rw [qTwist_qExpand]
    have : ((-1 : ℚˣ) ^ ((2 : ℕ) : ℤ)) = 1 := by
      rw [zpow_natCast]; exact neg_one_sq
    rw [this, qTwist_one_apply]
  have hB : qExpand ℚ 2 jq * v ^ 2 * (16 * v - 1) ^ 2 = (256 * v ^ 2 - 16 * v + 1) ^ 3 := by
    have h := congrArg (qTwist (-1 : ℚˣ)) hJΛ
    simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, heven] using h

  have hP : (256 * v ^ 2 - 16 * v + 1) ^ 3 * (u ^ 2 * (16 * u - 1) ^ 2)
      - (256 * u ^ 2 - 16 * u + 1) ^ 3 * (v ^ 2 * (16 * v - 1) ^ 2) = 0 := by
    rw [← hB, ← hJΛ]; ring
  have hfac : (256 * v ^ 2 - 16 * v + 1) ^ 3 * (u ^ 2 * (16 * u - 1) ^ 2)
      - (256 * u ^ 2 - 16 * u + 1) ^ 3 * (v ^ 2 * (16 * v - 1) ^ 2)
      = -((u - v) * (256 * u * v - 1) * (16 * u + 16 * v - 1) * (16 * u * v - u - v)
          * (256 * u * v - 16 * u + 1) * (256 * u * v - 16 * v + 1)) := by ring
  rw [hfac, neg_eq_zero] at hP

  have hus : SuppGE 1 u := suppGE_mu
  have hvs : SuppGE 1 v := suppGE_v
  have huv : SuppGE 1 (u * v) := SuppGE.mono (by norm_num) (hus.mul hvs)
  have c_uv : ∀ (m : ℕ) [m.AtLeastTwo], ((OfNat.ofNat m : L) * u * v).coeff 0 = 0 := by
    intro m _
    rw [mul_assoc]; exact coeff_zero_ofNat_mul huv m
  simp only [mul_eq_zero] at hP
  rcases hP with ((((h1 | h2) | h3) | h4) | h5) | h6
  · exfalso
    have h := congrArg (fun x : L => x.coeff 1) h1
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero] at h
    rw [hu, hv, coeff_mu_one, coeff_v_one] at h
    norm_num at h
  · exfalso
    have h := congrArg (fun x : L => x.coeff 0) h2
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero] at h
    rw [c_uv 256, coeff_one_zero] at h
    norm_num at h
  · exfalso
    have h := congrArg (fun x : L => x.coeff 0) h3
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_zero] at h
    rw [coeff_zero_ofNat_mul hus 16, coeff_zero_ofNat_mul hvs 16, coeff_one_zero] at h
    norm_num at h
  ·
    linear_combination h4
  · exfalso
    have h := congrArg (fun x : L => x.coeff 0) h5
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_zero] at h
    rw [c_uv 256, coeff_zero_ofNat_mul hus 16, coeff_one_zero] at h
    norm_num at h
  · exfalso
    have h := congrArg (fun x : L => x.coeff 0) h6
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_zero] at h
    rw [c_uv 256, coeff_zero_ofNat_mul hvs 16, coeff_one_zero] at h
    norm_num at h

theorem laurentMap_qTwist_neg_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    laurentMap f (qTwist (-1 : Rˣ) x) = qTwist (-1 : Sˣ) (laurentMap f x) := by
  ext k
  rw [laurentMap_coeff, qTwist_coeff, qTwist_coeff, laurentMap_coeff, map_mul]
  congr 1
  have e : Units.map (f : R →* S) (-1 : Rˣ) = (-1 : Sˣ) := by
    apply Units.ext
    rw [Units.coe_map, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one]
    show f (-1) = -1
    rw [map_neg, map_one]
  calc f (((-1 : Rˣ) ^ k : Rˣ) : R) = ((Units.map (f : R →* S) ((-1 : Rˣ) ^ k) : Sˣ) : S) :=
        (Units.coe_map (f : R →* S) ((-1 : Rˣ) ^ k)).symm
    _ = (((Units.map (f : R →* S) (-1 : Rˣ)) ^ k : Sˣ) : S) := by rw [map_zpow]
    _ = (((-1 : Sˣ) ^ k : Sˣ) : S) := by rw [e]

theorem muneg (K : Type*) [CommRing K] :
    qTwist (-1 : Kˣ) (lambdaModC K) * (16 * lambdaModC K - 1) = lambdaModC K := by

  have hZ : qTwist (-1 : ℤˣ) lambdaInt * (16 * lambdaInt - 1) = lambdaInt := by
    apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [map_mul, laurentMap_qTwist_neg_one, map_sub, map_mul, map_ofNat, map_one]
    exact muneg_rat

  show qTwist (-1 : Kˣ) (laurentMap (Int.castRingHom K) lambdaInt)
      * (16 * laurentMap (Int.castRingHom K) lambdaInt - 1) = laurentMap (Int.castRingHom K) lambdaInt
  rw [← laurentMap_qTwist_neg_one]
  conv_rhs => rw [← hZ]
  rw [map_mul, map_sub, map_mul, map_ofNat, map_one]

end Muneg

end LambdaE2Sol

end

open ModularCurve ModularCurve.PhiGen in
theorem solution (K : Type*) [CommRing K] :
    qTwist (-1 : Kˣ) (lambdaModC K) * (16 * lambdaModC K - 1) = lambdaModC K :=
  LambdaE2Sol.muneg K

end S_ModularCurve_qTwist_neg_one_lambdaModC_mul
end P2MW
export P2MW.S_ModularCurve_qTwist_neg_one_lambdaModC_mul (solution)
